-- Prove2me | solution 1 for MIPRE.Cost.efficient_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:47:21.349926+00:00
-- url     : https://prove2.me/submissions/4d794118-98d2-4678-b1a4-d6b599d7dd6e

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Kleene.lean (solution of MIPRE.Cost.efficient_fixed_point);
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
import Theorems.Thm_MIPRE_Cost_Prog_kleeneProg_halts_of
import Theorems.Thm_MIPRE_Cost_Prog_kleeneProg_runs
import Theorems.Thm_MIPRE_Cost_exists_efficient_universal
import Theorems.Thm_MIPRE_Cost_hardcode_time
import Theorems.Thm_MIPRE_Cost_hardcode_time_rev
import Theorems.Thm_MIPRE_Cost_kleeneFix_runs_of

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost
open Polynomial
theorem hardcode_wellScoped {p : Prog} (hp : p.WellScoped 1) (d : Data) :
    (hardcode p d).WellScoped 1 :=
  ⟨⟨trivial, Nat.zero_lt_one⟩, hp.mono (by omega) _⟩
end MIPRE.Cost

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

namespace MIPRE.Cost
open Polynomial
theorem kleeneFix_wellScoped (U : UniversalMachine) (F : PolyTimeFun Prog Prog) :
    (kleeneFix U F).WellScoped 1 :=
  hardcode_wellScoped (Prog.kleeneProg_wellScoped U.closed F) _
end MIPRE.Cost

namespace MIPRE.Cost
open Polynomial
/-- The fixed point has the input/output behavior of `F` applied to it. -/
theorem kleeneFix_halts_iff (U : UniversalMachine) (F : PolyTimeFun Prog Prog) (v r : Data) :
    (∃ t, (kleeneFix U F).Runs v r t) ↔ ∃ t, (F (kleeneFix U F)).Runs v r t := by
  have hGw : (Prog.kleeneProg U.univ F).WellScoped 1 := Prog.kleeneProg_wellScoped U.closed F
  constructor
  · rintro ⟨t', h⟩
    obtain ⟨T, -, hT⟩ := hardcode_time_rev hGw h
    exact Prog.kleeneProg_halts_of U F _ hT
  · rintro ⟨t, h⟩
    obtain ⟨T, -, hT⟩ := Prog.kleeneProg_runs U F _ h
    exact ⟨_, hardcode_time hGw hT⟩
end MIPRE.Cost

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open Polynomial
theorem solution (F : PolyTimeFun Prog Prog) :
    ∃ (e : Prog) (p : Polynomial ℕ),
      e.WellScoped 1 ∧
      (∀ v r, (∃ t, e.Runs v r t) ↔ ∃ t, (F e).Runs v r t) ∧
      ∀ v r t, (F e).Runs v r t → ∃ t' ≤ p.eval (v.size + t), e.Runs v r t' := by
  obtain ⟨U⟩ := exists_efficient_universal
  refine ⟨kleeneFix U F,
    U.bound.comp (X + C (esize (F (kleeneFix U F)))) + C 3 * X + C (kleeneOverhead U F),
    kleeneFix_wellScoped U F, kleeneFix_halts_iff U F, fun v r t h => ?_⟩
  obtain ⟨t', ht', hrun⟩ := kleeneFix_runs_of U F h
  refine ⟨t', ?_, hrun⟩
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.eval_X, Polynomial.eval_C]
  omega
