-- Prove2me | solution 1 for MIPRE.SAT.Fml.toCircuit_wellFormed
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:54:19.129203+00:00
-- url     : https://prove2.me/submissions/8aa759f6-efc5-4278-82f8-2eba77f7aab8

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Formula.lean (solution of MIPRE.SAT.Fml.toCircuit_wellFormed);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Theorems.Thm_MIPRE_SAT_Fml_refCount_flattenAt_le
import Theorems.Thm_MIPRE_SAT_Fml_refs_flattenAt
import Theorems.Thm_MIPRE_SAT_Fml_size_pos

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT.Fml
section
open Cost
/-- A gate list whose references at position `k` are in `[base, base + k)` references no `u`
outside `[base, base + length - 1)`. -/
theorem refCount_eq_zero_of_forall (gs : List Gate) (u : ℕ)
    (h : ∀ (k : ℕ) (hk : k < gs.length), u ∉ gs[k].refs) : refCount gs u = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [refCount, List.map_cons, List.sum_cons]
    have h0 : u ∉ g.refs := h 0 (by simp)
    rw [List.count_eq_zero.mpr h0, Nat.zero_add]
    exact ih fun k hk => h (k + 1) (by simpa using hk)
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem refCount_flattenAt_eq_zero (base : ℕ) (f : Fml) (u : ℕ)
    (hu : u < base ∨ base + f.size - 1 ≤ u) : refCount (f.flattenAt base) u = 0 := by
  apply refCount_eq_zero_of_forall
  intro k hk hmem
  have := refs_flattenAt base f k hk u hmem
  simp only [length_flattenAt] at hk
  omega
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem inputsLt_of_mem_flattenAt {n : ℕ} (base : ℕ) :
    ∀ (f : Fml), f.InputsLt n → ∀ i, Gate.input i ∈ f.flattenAt base → i < n
  | inp j, hf, i, hi => by simp [flattenAt] at hi; subst hi; exact hf
  | const _, _, i, hi => by simp [flattenAt] at hi
  | and f g, ⟨hf, hg⟩, i, hi => by
    simp only [flattenAt, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hi
    rcases hi with hi | hi
    · exact inputsLt_of_mem_flattenAt base f hf i hi
    · exact inputsLt_of_mem_flattenAt _ g hg i hi
  | or f g, ⟨hf, hg⟩, i, hi => by
    simp only [flattenAt, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hi
    rcases hi with hi | hi
    · exact inputsLt_of_mem_flattenAt base f hf i hi
    · exact inputsLt_of_mem_flattenAt _ g hg i hi
  | not f, hf, i, hi => by
    simp only [flattenAt, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hi
    exact inputsLt_of_mem_flattenAt base f hf i hi
end
end MIPRE.SAT.Fml

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.Fml
open Cost
theorem _root_.solution {n : ℕ} (f : Fml) (hf : f.InputsLt n) : (f.toCircuit n).WellFormed where
  refs_lt k hk u hu := by have := (refs_flattenAt 0 f k hk u hu).2; omega
  inputs_lt i hi := inputsLt_of_mem_flattenAt 0 f hf i hi
  fanout_le u := (refCount_flattenAt_le 0 f u).trans (by omega)
  output_terminal := by
    show refCount (f.flattenAt 0) ((f.flattenAt 0).length - 1) = 0
    rw [length_flattenAt]
    exact refCount_flattenAt_eq_zero 0 f _ (Or.inr (by omega))
  nonempty := by
    intro h
    have h1 := length_flattenAt 0 f
    have h2 := f.size_pos
    have h' : f.flattenAt 0 = [] := h
    rw [h'] at h1
    simp only [List.length_nil] at h1
    omega
end MIPRE.SAT.Fml
