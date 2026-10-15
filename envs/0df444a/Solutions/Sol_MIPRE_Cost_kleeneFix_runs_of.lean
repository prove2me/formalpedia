-- Prove2me | solution 1 for MIPRE.Cost.kleeneFix_runs_of
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:35:05.411563+00:00
-- url     : https://prove2.me/submissions/fc712b1b-5496-4c71-b385-1afb4554ec2f

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Kleene.lean (solution of MIPRE.Cost.kleeneFix_runs_of);
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
import Theorems.Thm_MIPRE_Cost_Prog_kleeneProg_runs
import Theorems.Thm_MIPRE_Cost_hardcode_time

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost.Prog
open Polynomial
theorem kleeneProg_wellScoped {univ : Prog} (hU : univ.WellScoped 1) (F : PolyTimeFun Prog Prog) :
    (kleeneProg univ F).WellScoped 1 :=
  ⟨by decide, trivial, ⟨by simp [WellScoped], by simp [WellScoped]⟩,
    callVar_wellScoped (by decide) smnProg_wellScoped,
    callVar_wellScoped (by decide) F.closed,
    ⟨by simp [WellScoped], by simp [WellScoped]⟩,
    callVar_wellScoped (by decide) hU⟩
end MIPRE.Cost.Prog

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open Polynomial
theorem solution (U : UniversalMachine) (F : PolyTimeFun Prog Prog) {v r : Data}
    {t : ℕ} (h : (F (kleeneFix U F)).Runs v r t) :
    ∃ t' ≤ U.bound.eval (v.size + t + esize (F (kleeneFix U F))) + 3 * v.size +
        kleeneOverhead U F,
      (kleeneFix U F).Runs v r t' := by
  have hGw : (Prog.kleeneProg U.univ F).WellScoped 1 := Prog.kleeneProg_wellScoped U.closed F
  obtain ⟨T, hT, hrun⟩ := Prog.kleeneProg_runs U F _ h
  refine ⟨_, ?_, hardcode_time hGw hrun⟩
  have hT' : T ≤ 6 * esize (Prog.kleeneProg U.univ F) + esize (kleeneFix U F) +
      F.timeBound.eval (esize (kleeneFix U F)) + 2 * esize (F (kleeneFix U F)) + 2 * v.size +
      U.bound.eval (esize (F (kleeneFix U F)) + v.size + t) + 57 := hT
  have e1 : (encode (Prog.kleeneProg U.univ F)).size = esize (Prog.kleeneProg U.univ F) := rfl
  have hm := polynomial_eval_mono U.bound
    (show esize (F (kleeneFix U F)) + v.size + t ≤ v.size + t + esize (F (kleeneFix U F)) by
      omega)
  rw [kleeneOverhead]
  omega
