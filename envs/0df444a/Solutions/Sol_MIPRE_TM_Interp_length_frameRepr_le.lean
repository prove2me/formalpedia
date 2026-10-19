-- Prove2me | solution 1 for MIPRE.TM.Interp.length_frameRepr_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:53:38.829741+00:00
-- url     : https://prove2.me/submissions/2da345ae-bc31-4c4a-86c9-4a4ddb3f9241

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Repr.lean (solution of MIPRE.TM.Interp.length_frameRepr_le);
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
theorem length_envRepr (env : Env) :
    (envRepr env).length = (env.map Data.size).sum + env.length := by
  induction env with
  | nil => simp
  | cons v env ih => simp [ih]; omega
end
end MIPRE.TM.Interp

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.Interp
open MIPRE.Cost MIPRE.Cost.Machine
theorem _root_.solution {V L P : ℕ} {f : Frame} (h : FrameBound V L P f) :
    (frameRepr f).length ≤ V + P + L * V + L + 4 := by
  cases f with
  | cons2 a => simp only [FrameBound] at h; simp [frameRepr]; omega
  | cons1 t env =>
    obtain ⟨h1, h2, h3⟩ := h
    rw [Prog.esize_eq_size_toData] at h1
    have := length_envRepr env
    have hsum : (env.map Data.size).sum ≤ L * V := by
      calc (env.map Data.size).sum ≤ (env.map fun _ => V).sum :=
            List.sum_le_sum (fun v hv => h3 v hv)
        _ = env.length * V := by simp [List.map_const', List.sum_replicate]
        _ ≤ L * V := Nat.mul_le_mul_right V h2
    simp only [frameRepr, List.length_append, List.length_cons, List.length_nil, length_S,
      List.length_singleton]
    omega
  | let1 b env =>
    obtain ⟨h1, h2, h3⟩ := h
    rw [Prog.esize_eq_size_toData] at h1
    have := length_envRepr env
    have hsum : (env.map Data.size).sum ≤ L * V := by
      calc (env.map Data.size).sum ≤ (env.map fun _ => V).sum :=
            List.sum_le_sum (fun v hv => h3 v hv)
        _ = env.length * V := by simp [List.map_const', List.sum_replicate]
        _ ≤ L * V := Nat.mul_le_mul_right V h2
    simp only [frameRepr, List.length_append, List.length_cons, List.length_nil, length_S,
      List.length_singleton]
    omega
  | loop1 b env =>
    obtain ⟨h1, h2, h3⟩ := h
    rw [Prog.esize_eq_size_toData] at h1
    have := length_envRepr env
    have hsum : (env.map Data.size).sum ≤ L * V := by
      calc (env.map Data.size).sum ≤ (env.map fun _ => V).sum :=
            List.sum_le_sum (fun v hv => h3 v hv)
        _ = env.length * V := by simp [List.map_const', List.sum_replicate]
        _ ≤ L * V := Nat.mul_le_mul_right V h2
    simp only [frameRepr, List.length_append, List.length_cons, List.length_nil, length_S,
      List.length_singleton]
    omega
end MIPRE.TM.Interp
