-- Prove2me | solution 1 for MIPRE.Cost.Prog.coordLoop_inv
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:37:11.125211+00:00
-- url     : https://prove2.me/submissions/995aa7fa-45f8-49fe-ae3f-bc06186fabe5

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/DecLoop.lean (solution of MIPRE.Cost.Prog.coordLoop_inv);
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
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_Eval_of_append_of_wellScoped
import Theorems.Thm_MIPRE_Cost_Prog_coordBody_inv
import Theorems.Thm_MIPRE_Cost_Prog_preProg_runs
import Theorems.Thm_MIPRE_Cost_Prog_preProg_runs_nilB
import Theorems.Thm_MIPRE_Cost_Prog_stepProg_inv

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Prog
section
open Data
theorem bitWalkBody_wellScoped : bitWalkBody.WellScoped 1 := by
  simp [bitWalkBody, WellScoped]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem bitWalkProg_wellScoped : bitWalkProg.WellScoped 1 :=
  ⟨Nat.zero_lt_one, bitWalkBody_wellScoped⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem pairTakeProg_wellScoped : pairTakeProg.WellScoped 1 := by
  simp [pairTakeProg, WellScoped, takeBody, callVar, revProg, revOntoProg, revOntoBody]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem finalProg_wellScoped : finalProg.WellScoped 1 := by simp [finalProg, WellScoped]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem preProg_wellScoped : preProg.WellScoped 1 := by
  simp only [preProg, WellScoped, callVar]
  refine ⟨by omega, trivial, by omega, trivial, by omega, trivial, by omega, trivial, by omega,
    trivial, by omega, trivial, by omega, trivial, by omega, trivial, by omega, trivial, by omega,
    trivial, ⟨by omega, by omega, by omega⟩, ⟨by omega, pairTakeProg_wellScoped.mono (by omega) _⟩,
    ⟨by omega, by omega⟩, ⟨by omega, bitWalkProg_wellScoped.mono (by omega) _⟩, by omega, trivial,
    by omega, ⟨⟨by omega, by omega⟩, ⟨by omega, bitWalkProg_wellScoped.mono (by omega) _⟩, by omega,
      trivial, by omega, ⟨by omega, trivial, by omega, trivial, by omega, trivial,
        ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩,
        ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩⟩, trivial⟩, trivial⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem preProg_runs_nilA (uk : Data) (remX remY remB : List Data) (ctx : Data) :
    ∃ t ≤ 7, Eval [decState uk remX remY [] remB ctx] preProg .nil t :=
  ⟨7, le_rfl, Eval.elim_cons (i := 0) (n := .nil) (a := uk)
    (b := .cons (list remX) (.cons (list remY) (.cons (list []) (.cons (list remB) ctx))))
    (by simp [decState])
    (Eval.elim_cons (i := 1) (n := .nil) (a := list remX)
      (b := .cons (list remY) (.cons (list []) (.cons (list remB) ctx))) (by simp)
      (Eval.elim_cons (i := 1) (n := .nil) (a := list remY)
        (b := .cons (list []) (.cons (list remB) ctx)) (by simp)
        (Eval.elim_cons (i := 1) (n := .nil) (a := list []) (b := .cons (list remB) ctx) (by simp)
          (Eval.elim_cons (i := 1) (n := .nil) (a := list remB) (b := ctx) (by simp)
            (Eval.elim_nil (i := 2) (by simp) (Eval.nil _))))))⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem stepProg_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (stepProg univ).WellScoped 1 := by
  simp only [stepProg, WellScoped, callVar]
  exact ⟨⟨by omega, preProg_wellScoped.mono (by omega) _⟩, by omega, ⟨trivial, trivial⟩,
    ⟨by omega, hU.mono (by omega) _⟩, by omega, ⟨trivial, trivial⟩, by omega, ⟨by omega,
      ⟨⟨trivial, trivial⟩, by omega⟩, ⟨trivial, trivial⟩⟩, ⟨trivial, trivial⟩⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem coordBody_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (coordBody univ).WellScoped 1 := by
  simp only [coordBody, WellScoped, callVar]
  exact ⟨by omega, trivial, by omega, ⟨by omega, finalProg_wellScoped.mono (by omega) _⟩,
    ⟨by omega, by omega⟩, by omega, (stepProg_wellScoped hU).mono (by omega) _⟩
end
end MIPRE.Cost.Prog

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution {univ : Prog} (hU : univ.WellScoped 1) (dD nD : Data) (s B : ℕ) :
    ∀ (k : ℕ) (remX remY remA remB : List Data) (env : Env) {t : ℕ},
      Eval (decState (ofNat k) remX remY remA remB (decCtx dD nD s B) :: env)
        (.loop (coordBody univ)) (.cons .nil .nil) t →
      DecAcc univ dD nD s B k remX remY remA remB := by
  intro k
  induction k with
  | zero =>
    intro remX remY remA remB env t h
    cases h with
    | loop_stop hb =>
      have hb' := Eval.of_append_of_wellScoped (env := [_]) hb (coordBody_wellScoped hU)
      rcases coordBody_inv hU 0 remX remY remA remB _ hb' with ⟨-, h⟩ | ⟨k', hk, -⟩
      · simp only [Data.cons.injEq, true_and] at h
        show remA = [] ∧ remB = []
        rcases hd : decide (remA = [] ∧ remB = []) with _ | _
        · rw [hd] at h; cases h
        · exact of_decide_eq_true hd
      · omega
    | loop_step hb _ =>
      have hb' := Eval.of_append_of_wellScoped (env := [_]) hb (coordBody_wellScoped hU)
      rcases coordBody_inv hU 0 remX remY remA remB _ hb' with ⟨-, h⟩ | ⟨k', hk, -⟩
      · cases h
      · omega
  | succ k ih =>
    intro remX remY remA remB env t h
    cases h with
    | loop_stop hb =>
      have hb' := Eval.of_append_of_wellScoped (env := [_]) hb (coordBody_wellScoped hU)
      rcases coordBody_inv hU (k + 1) remX remY remA remB _ hb' with ⟨h0, -⟩ | ⟨k', hk, t', hs⟩
      · omega
      · obtain rfl : k = k' := by omega
        obtain ⟨p, t₀, -, hcase⟩ := stepProg_inv hU _ hs
        rcases hcase with ⟨-, h⟩ | ⟨q, st', r, -, -, h⟩
        · cases h
        · simp only [stepResult] at h
          split_ifs at h <;> cases h
    | loop_step hb hrest =>
      rename_i x y v s₁ t₁
      have hb' := Eval.of_append_of_wellScoped (env := [_]) hb (coordBody_wellScoped hU)
      rcases coordBody_inv hU (k + 1) remX remY remA remB _ hb' with ⟨h0, -⟩ | ⟨k', hk, t', hs⟩
      · omega
      · obtain rfl : k = k' := by omega
        obtain ⟨p, t₀, hp, hcase⟩ := stepProg_inv hU _ hs
        rcases hcase with ⟨-, h⟩ | ⟨q, st', r, rfl, ⟨tr, hr⟩, h⟩
        · cases h
        · -- the query and the next state are those of `preProg`
          rcases remA with _ | ⟨ai, remA'⟩
          · obtain ⟨t₂, -, h₂⟩ := preProg_runs_nilA (ofNat k) remX remY remB (decCtx dD nD s B)
            cases (hp.deterministic h₂).1
          rcases remB with _ | ⟨bi, remB'⟩
          · obtain ⟨t₂, -, h₂⟩ := preProg_runs_nilB (ofNat k) remX remY ai remA' (decCtx dD nD s B)
            cases (hp.deterministic h₂).1
          obtain ⟨t₂, -, h₂⟩ := preProg_runs dD nD s B (ofNat k) remX remY ai bi remA' remB'
          have hpq := (hp.deterministic h₂).1
          simp only [preResult] at hpq
          split_ifs at hpq with hok
          · simp only [Data.cons.injEq] at hpq
            obtain ⟨rfl, rfl⟩ := hpq
            simp only [Bool.and_eq_true] at hok
            simp only [stepResult] at h
            split_ifs at h with hr1
            · subst hr1
              simp only [Data.cons.injEq] at h
              obtain ⟨-, rfl⟩ := h
              refine ⟨hok.1, hok.2, ⟨tr, hr⟩, ?_⟩
              exact ih _ _ _ _ env hrest
            · cases h
end MIPRE.Cost.Prog
