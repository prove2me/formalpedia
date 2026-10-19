-- Prove2me | solution 1 for MIPRE.SAT.Fml.refCount_flattenAt_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:52:32.690991+00:00
-- url     : https://prove2.me/submissions/88b24908-ca8e-4122-af77-5f09e797bb8d

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Formula.lean (solution of MIPRE.SAT.Fml.refCount_flattenAt_le);
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.Fml
open Cost
theorem _root_.solution (base : ℕ) : ∀ (f : Fml) (u : ℕ), refCount (f.flattenAt base) u ≤ 1
  | inp _, u => by simp [flattenAt, Gate.refs]
  | const _, u => by simp [flattenAt, Gate.refs]
  | and f g, u => by
    have hfp := f.size_pos
    have hgp := g.size_pos
    simp only [flattenAt, refCount_append, refCount_singleton, Gate.refs]
    have hf := solution base f u
    have hg := solution (base + f.size) g u
    have hf0 := refCount_flattenAt_eq_zero base f u
    have hg0 := refCount_flattenAt_eq_zero (base + f.size) g u
    by_cases h1 : u = base + f.size - 1
    · rw [hf0 (by omega), hg0 (by omega)]
      subst h1
      simp only [List.count_cons, List.count_nil, beq_iff_eq]
      split_ifs <;> omega
    · by_cases h2 : u = base + f.size + g.size - 1
      · rw [hf0 (by omega), hg0 (by omega)]
        subst h2
        simp only [List.count_cons, List.count_nil, beq_iff_eq]
        split_ifs <;> omega
      · have : List.count u [base + f.size - 1, base + f.size + g.size - 1] = 0 := by
          simp [Ne.symm h1, Ne.symm h2]
        rw [this]
        by_cases h3 : u < base + f.size
        · rw [hg0 (by omega)]; omega
        · rw [hf0 (by omega)]; omega
  | or f g, u => by
    have hfp := f.size_pos
    have hgp := g.size_pos
    simp only [flattenAt, refCount_append, refCount_singleton, Gate.refs]
    have hf := solution base f u
    have hg := solution (base + f.size) g u
    have hf0 := refCount_flattenAt_eq_zero base f u
    have hg0 := refCount_flattenAt_eq_zero (base + f.size) g u
    by_cases h1 : u = base + f.size - 1
    · rw [hf0 (by omega), hg0 (by omega)]
      subst h1
      simp only [List.count_cons, List.count_nil, beq_iff_eq]
      split_ifs <;> omega
    · by_cases h2 : u = base + f.size + g.size - 1
      · rw [hf0 (by omega), hg0 (by omega)]
        subst h2
        simp only [List.count_cons, List.count_nil, beq_iff_eq]
        split_ifs <;> omega
      · have : List.count u [base + f.size - 1, base + f.size + g.size - 1] = 0 := by
          simp [Ne.symm h1, Ne.symm h2]
        rw [this]
        by_cases h3 : u < base + f.size
        · rw [hg0 (by omega)]; omega
        · rw [hf0 (by omega)]; omega
  | not f, u => by
    have hfp := f.size_pos
    simp only [flattenAt, refCount_append, refCount_singleton, Gate.refs]
    have hf := solution base f u
    have hf0 := refCount_flattenAt_eq_zero base f u
    by_cases h1 : u = base + f.size - 1
    · rw [hf0 (by omega)]; subst h1; simp
    · have : List.count u [base + f.size - 1] = 0 := by simp [List.count_cons, Ne.symm h1]
      rw [this]; omega
end MIPRE.SAT.Fml
