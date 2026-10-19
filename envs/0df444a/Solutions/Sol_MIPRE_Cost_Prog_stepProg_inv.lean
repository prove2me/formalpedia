-- Prove2me | solution 1 for MIPRE.Cost.Prog.stepProg_inv
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:32:45.524987+00:00
-- url     : https://prove2.me/submissions/ee5965b0-00c4-4bac-9dac-dc803d93d037

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/DecLoop.lean (solution of MIPRE.Cost.Prog.stepProg_inv);
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution {univ : Prog} (hU : univ.WellScoped 1) (inp : Data) {out : Data} {t : ℕ}
    (h : Eval [inp] (stepProg univ) out t) :
    ∃ p t₀, Eval [inp] preProg p t₀ ∧
      ((p = .nil ∧ out = .cons .nil .nil) ∨
        ∃ q st' r, p = .cons q st' ∧ (∃ tr, Eval [q] univ r tr) ∧ out = stepResult st' r) := by
  change Eval [inp] (.let_ (callVar 0 preProg) _) out t at h
  cases h with
  | let_ hA hB =>
    obtain ⟨t₀, -, hp⟩ := callVar_runs_rev preProg_wellScoped hA
    refine ⟨_, t₀, hp, ?_⟩
    cases hB with
    | elim_nil hn hc =>
      refine Or.inl ⟨by simpa using hn, ?_⟩
      cases hc with
      | cons h1 h2 => cases h1; cases h2; rfl
    | @elim_cons _ _ _ _ q st' _ _ hc hd =>
      refine Or.inr ⟨q, st', ?_⟩
      cases hd with
      | let_ hC hD =>
        obtain ⟨tr, -, hr⟩ := callVar_runs_rev hU hC
        simp only [Env.get_cons_zero] at hr
        refine ⟨_, by simpa using hc, ⟨tr, hr⟩, ?_⟩
        cases hD with
        | elim_nil hn he =>
          simp only [Env.get_cons_zero] at hn
          subst hn
          cases he with
          | cons h1 h2 => cases h1; cases h2; rfl
        | @elim_cons _ _ _ _ r0 r1 _ _ hc2 he =>
          simp only [Env.get_cons_zero] at hc2
          subst hc2
          cases he with
          | elim_nil hn2 hf =>
            simp only [Env.get_cons_zero] at hn2
            subst hn2
            cases hf with
            | elim_nil hn3 hg =>
              simp only [Env.get_cons_succ, Env.get_cons_zero] at hn3
              subst hn3
              cases hg with
              | cons h1 h2 =>
                cases h1 with
                | cons h3 h4 => cases h3; cases h4; cases h2; rfl
            | elim_cons hc3 hg =>
              simp only [Env.get_cons_succ, Env.get_cons_zero] at hc3
              subst hc3
              cases hg with
              | cons h1 h2 => cases h1; cases h2; simp [stepResult]
          | elim_cons hc2' hf =>
            simp only [Env.get_cons_zero] at hc2'
            subst hc2'
            cases hf with
            | cons h1 h2 => cases h1; cases h2; simp [stepResult]
end MIPRE.Cost.Prog
