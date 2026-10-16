-- Prove2me | solution 1 for MIPRE.Cost.halts_haltingReduction_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T19:55:52.046404+00:00
-- url     : https://prove2.me/submissions/ac6ba32d-6eaa-4d95-be46-3b2e84adec22

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/ManyOne.lean (solution of MIPRE.Cost.halts_haltingReduction_iff);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
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
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_Partrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Semidecide
import Definitions.Def_MIPRE_Foundations_Cost_ManyOne
import Theorems.Thm_MIPRE_Cost_hardcode_time
import Theorems.Thm_MIPRE_Cost_hardcode_time_rev

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost
theorem Prog.onLeft_wellScoped {p : Prog} (hp : p.WellScoped 1) : (Prog.onLeft p).WellScoped 1 :=
  ⟨by decide, trivial, Prog.callVar_wellScoped (by decide) hp⟩
end MIPRE.Cost

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost
theorem _root_.solution {S : Prog} (hS : S.WellScoped 1) (z : BitStr) :
    Halts (haltingReduction S z) .nil ↔ Halts S (encode z) := by
  have hw := Prog.onLeft_wellScoped hS
  constructor
  · rintro ⟨r, t, h⟩
    obtain ⟨t', -, h'⟩ := hardcode_time_rev hw h
    change Eval [Data.cons (encode z) .nil] (.elim 0 .nil _) r t' at h'
    cases h' with
    | elim_nil hget _ => simp at hget
    | elim_cons hget h₁ =>
      rw [Env.get_cons_zero] at hget
      obtain ⟨rfl, rfl⟩ := Data.cons.inj hget
      obtain ⟨t'', -, hp⟩ := Prog.callVar_runs_rev hS h₁
      rw [Env.get_cons_zero] at hp
      exact ⟨r, t'', hp⟩
  · rintro ⟨r, t, h⟩
    have h₁ := Prog.callVar_eval (env := [encode z, .nil, Data.cons (encode z) .nil]) (i := 0) hS
      (v := encode z) (by simp) h
    have h₂ := Eval.elim_cons (env := [Data.cons (encode z) .nil]) (i := 0) (n := .nil)
      (a := encode z) (b := .nil) (by simp) h₁
    exact ⟨r, _, hardcode_time hw h₂⟩
end MIPRE.Cost
