-- Prove2me | solution 1 for MIPRE.Cost.Prog.stepProg_runs_call
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:32:44.851872+00:00
-- url     : https://prove2.me/submissions/6fe900ab-d2e2-4f52-b0f1-4989f2a5d618

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/DecLoop.lean (solution of MIPRE.Cost.Prog.stepProg_runs_call);
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
theorem _root_.solution {univ : Prog} (hU : univ.WellScoped 1) (inp q st' : Data) {t₀ : ℕ}
    (hp : Eval [inp] preProg (.cons q st') t₀) {r : Data} {tr : ℕ} (hr : Eval [q] univ r tr) :
    ∃ t ≤ t₀ + tr + inp.size + q.size + st'.size + 20,
      Eval [inp] (stepProg univ) (stepResult st' r) t := by
  have hpre : ∀ {out : Data} {t : ℕ},
      Eval [r, q, st', .cons q st', inp]
        (.elim 0 (.cons .nil .nil)
          (.elim 0 (.elim 1 (.cons (.cons .nil .nil) (.var 4)) (.cons .nil .nil))
            (.cons .nil .nil))) out t →
      Eval [inp] (stepProg univ) out (t₀ + inp.size + q.size + tr + t + 7) := by
    intro out t hc
    have run : Eval [inp] (stepProg univ) out _ :=
      Eval.let_ (callVar_eval preProg_wellScoped (i := 0) (v := inp) rfl hp)
        (Eval.elim_cons (i := 0) (n := .cons .nil .nil) (a := q) (b := st') rfl
          (Eval.let_ (callVar_eval hU (i := 0) (v := q) rfl hr) hc))
    exact run.cast_cost (by omega)
  rcases r with _ | ⟨_ | ⟨a, b⟩, _ | ⟨c, d⟩⟩
  · refine ⟨_, ?_, hpre (Eval.elim_nil (i := 0) (by simp) (Eval.cons (Eval.nil _) (Eval.nil _)))⟩
    omega
  · refine ⟨_, ?_, hpre (Eval.elim_cons (i := 0) (a := .nil) (b := .nil) (by simp)
      (Eval.elim_nil (i := 0) (by simp) (Eval.elim_nil (i := 1) (by simp)
        (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
          (Eval.var_of_get (i := 4) (v := st') (by simp))))))⟩
    omega
  · refine ⟨_, ?_, hpre (Eval.elim_cons (i := 0) (a := .nil) (b := .cons c d) (by simp)
      (Eval.elim_nil (i := 0) (by simp) (Eval.elim_cons (i := 1) (a := c) (b := d) (by simp)
        (Eval.cons (Eval.nil _) (Eval.nil _)))))⟩
    omega
  · refine ⟨_, ?_, hpre (Eval.elim_cons (i := 0) (a := .cons a b) (b := .nil) (by simp)
      (Eval.elim_cons (i := 0) (a := a) (b := b) (by simp)
        (Eval.cons (Eval.nil _) (Eval.nil _))))⟩
    omega
  · refine ⟨_, ?_, hpre (Eval.elim_cons (i := 0) (a := .cons a b) (b := .cons c d) (by simp)
      (Eval.elim_cons (i := 0) (a := a) (b := b) (by simp)
        (Eval.cons (Eval.nil _) (Eval.nil _))))⟩
    omega
end MIPRE.Cost.Prog
