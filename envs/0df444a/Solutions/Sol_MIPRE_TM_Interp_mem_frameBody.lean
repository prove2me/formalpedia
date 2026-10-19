-- Prove2me | solution 1 for MIPRE.TM.Interp.mem_frameBody
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:52:39.639129+00:00
-- url     : https://prove2.me/submissions/8b5cd42d-4829-401a-9f74-cd179e9847ac

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Repr.lean (solution of MIPRE.TM.Interp.mem_frameBody);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Tape
import Definitions.Def_MIPRE_TM_Interp_Repr

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TM.Interp
section
open MIPRE.Cost MIPRE.Cost.Machine
/-- The symbols of a value are bits. -/
theorem mem_S (v : Data) : ∀ s ∈ S v, s = .zero ∨ s = .one := by
  intro s hs
  simp only [S, bits, List.mem_map] at hs
  obtain ⟨b, -, rfl⟩ := hs
  cases b <;> simp
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open MIPRE.Cost MIPRE.Cost.Machine
/-- No `$` and no `¶` in an environment. -/
theorem mem_envRepr (env : Env) : ∀ s ∈ envRepr env, s ≠ .fr ∧ s ≠ .en := by
  induction env with
  | nil => simp
  | cons v env ih =>
    intro s hs
    simp only [envRepr_cons, List.mem_append, List.mem_singleton] at hs
    rcases hs with (hs | hs) | rfl
    · exact ih s hs
    · rcases mem_S v s hs with rfl | rfl <;> simp
    · simp
end
end MIPRE.TM.Interp

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.Interp
open MIPRE.Cost MIPRE.Cost.Machine
theorem _root_.solution (f : Frame) : ∀ s ∈ frameBody f, s ≠ .fr := by
  intro s hs
  have hS : ∀ v : Data, s ∈ S v → s ≠ .fr := fun v h =>
    (mem_S v s h).elim (fun e => e ▸ by simp) (fun e => e ▸ by simp)
  cases f with
  | cons1 t env =>
    simp only [frameBody, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hs
    rcases hs with (((rfl | rfl) | h) | rfl) | h
    · simp
    · simp
    · exact hS _ h
    · simp
    · exact (mem_envRepr env s h).1
  | cons2 a =>
    simp only [frameBody, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hs
    rcases hs with (rfl | rfl) | h
    · simp
    · simp
    · exact hS _ h
  | let1 b env =>
    simp only [frameBody, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hs
    rcases hs with (((rfl | rfl) | h) | rfl) | h
    · simp
    · simp
    · exact hS _ h
    · simp
    · exact (mem_envRepr env s h).1
  | loop1 b env =>
    simp only [frameBody, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hs
    rcases hs with (((rfl | rfl) | h) | rfl) | h
    · simp
    · simp
    · exact hS _ h
    · simp
    · exact (mem_envRepr env s h).1
end MIPRE.TM.Interp
