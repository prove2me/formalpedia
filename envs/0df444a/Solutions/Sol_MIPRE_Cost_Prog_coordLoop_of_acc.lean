-- Prove2me | solution 1 for MIPRE.Cost.Prog.coordLoop_of_acc
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:36:26.517723+00:00
-- url     : https://prove2.me/submissions/85bb81a8-09eb-42f7-a983-417970886504

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/DecLoop.lean (solution of MIPRE.Cost.Prog.coordLoop_of_acc);
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
import Theorems.Thm_MIPRE_Cost_Prog_coordBody_step
import Theorems.Thm_MIPRE_Cost_Prog_coordBody_stop
import Theorems.Thm_MIPRE_Cost_Prog_preProg_runs
import Theorems.Thm_MIPRE_Cost_Prog_stepProg_runs_call

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
    ∀ (k : ℕ) (remX remY remA remB : List Data) (env : Env),
      DecAcc univ dD nD s B k remX remY remA remB →
      ∃ t, Eval (decState (ofNat k) remX remY remA remB (decCtx dD nD s B) :: env)
        (.loop (coordBody univ)) (.cons .nil .nil) t
  | 0, remX, remY, remA, remB, env, hacc => by
    obtain ⟨rfl, rfl⟩ := hacc
    obtain ⟨t, -, h⟩ := coordBody_stop univ remX remY [] [] (decCtx dD nD s B)
    simp only [and_self, decide_true, ofBool] at h
    exact ⟨_, Eval.loop_stop (Eval.append_of_wellScoped h (coordBody_wellScoped hU) env)⟩
  | k + 1, remX, remY, [], remB, env, hacc => hacc.elim
  | k + 1, remX, remY, _ :: _, [], env, hacc => hacc.elim
  | k + 1, remX, remY, ai :: remA', bi :: remB', env, hacc => by
    obtain ⟨hoka, hokb, ⟨tr, hr⟩, hrec⟩ := hacc
    obtain ⟨t₀, -, hp⟩ := preProg_runs dD nD s B (ofNat k) remX remY ai bi remA' remB'
    rw [show preResult dD nD s B (ofNat k) remX remY ai bi remA' remB' =
        .cons (decQuery dD nD (list (remX.take s)) (list (remY.take s)) ai bi)
          (decState (ofNat k) (remX.drop s) (remY.drop s) remA' remB' (decCtx dD nD s B)) by
      simp [preResult, hoka, hokb]] at hp
    obtain ⟨t₁, -, h₁⟩ := stepProg_runs_call hU _ _ _ hp hr
    simp only [stepResult, if_true] at h₁
    have h₂ := coordBody_step hU k remX remY (ai :: remA') (bi :: remB') (decCtx dD nD s B) h₁
    obtain ⟨t₃, h₃⟩ := solution hU dD nD s B k (remX.drop s) (remY.drop s) remA' remB' env hrec
    exact ⟨_, Eval.loop_step (Eval.append_of_wellScoped h₂ (coordBody_wellScoped hU) env) h₃⟩
end MIPRE.Cost.Prog
