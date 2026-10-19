-- Prove2me | solution 1 for MIPRE.Cost.Prog.coordBody_inv
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:33:57.255649+00:00
-- url     : https://prove2.me/submissions/e66def80-2e8b-49b3-b133-f694784f01a3

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/DecLoop.lean (solution of MIPRE.Cost.Prog.coordBody_inv);
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
import Theorems.Thm_MIPRE_Cost_Prog_coordBody_stop

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
theorem stepProg_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (stepProg univ).WellScoped 1 := by
  simp only [stepProg, WellScoped, callVar]
  exact ⟨⟨by omega, preProg_wellScoped.mono (by omega) _⟩, by omega, ⟨trivial, trivial⟩,
    ⟨by omega, hU.mono (by omega) _⟩, by omega, ⟨trivial, trivial⟩, by omega, ⟨by omega,
      ⟨⟨trivial, trivial⟩, by omega⟩, ⟨trivial, trivial⟩⟩, ⟨trivial, trivial⟩⟩
end
end MIPRE.Cost.Prog

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution {univ : Prog} (hU : univ.WellScoped 1) (k : ℕ)
    (remX remY remA remB : List Data) (ctx : Data) {out : Data} {t : ℕ}
    (h : Eval [decState (ofNat k) remX remY remA remB ctx] (coordBody univ) out t) :
    (k = 0 ∧ out = .cons .nil (ofBool (decide (remA = [] ∧ remB = [])))) ∨
      ∃ k', k = k' + 1 ∧
        ∃ t', Eval [decState (ofNat k') remX remY remA remB ctx] (stepProg univ) out t' := by
  cases k with
  | zero =>
    obtain ⟨t₀, -, h₀⟩ := coordBody_stop univ remX remY remA remB ctx
    exact Or.inl ⟨rfl, (h.deterministic h₀).1⟩
  | succ k =>
    refine Or.inr ⟨k, rfl, ?_⟩
    change Eval _ (.elim 0 .nil _) out t at h
    cases h with
    | elim_nil hn _ => simp [decState] at hn
    | elim_cons hc h1 =>
      simp only [decState, Env.get_cons_zero, Data.cons.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      cases h1 with
      | elim_nil hn _ => simp [ofNat] at hn
      | elim_cons hc2 h2 =>
        simp only [Env.get_cons_zero, ofNat, Data.cons.injEq] at hc2
        obtain ⟨rfl, rfl⟩ := hc2
        cases h2 with
        | let_ hA hB =>
          obtain ⟨rfl, -⟩ := hA.deterministic (Eval.cons (Eval.var_of_get (i := 1) (v := ofNat k)
            (by simp)) (Eval.var_of_get (i := 3) (v := .cons (list remX) (.cons (list remY)
              (.cons (list remA) (.cons (list remB) ctx)))) (by simp)))
          obtain ⟨t', -, h'⟩ := callVar_runs_rev (stepProg_wellScoped hU) hB
          simp only [Env.get_cons_zero] at h'
          exact ⟨t', h'⟩
end MIPRE.Cost.Prog
