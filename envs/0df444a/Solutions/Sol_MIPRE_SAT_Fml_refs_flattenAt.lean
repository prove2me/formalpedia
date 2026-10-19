-- Prove2me | solution 1 for MIPRE.SAT.Fml.refs_flattenAt
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:50:56.380112+00:00
-- url     : https://prove2.me/submissions/770604b7-ab3c-419d-8ccf-e475aeefcd31

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Formula.lean (solution of MIPRE.SAT.Fml.refs_flattenAt);
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
import Theorems.Thm_MIPRE_SAT_Fml_size_pos

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.Fml
open Cost
theorem _root_.solution (base : ℕ) : ∀ (f : Fml) (k : ℕ) (hk : k < (f.flattenAt base).length),
    ∀ u ∈ (f.flattenAt base)[k].refs, base ≤ u ∧ u < base + k
  | inp _, k, hk, u, hu => by
    simp only [flattenAt, List.length_singleton] at hk
    obtain rfl : k = 0 := by omega
    simp [flattenAt, Gate.refs] at hu
  | const _, k, hk, u, hu => by
    simp only [flattenAt, List.length_singleton] at hk
    obtain rfl : k = 0 := by omega
    simp [flattenAt, Gate.refs] at hu
  | and f g, k, hk, u, hu => by
    have hf := length_flattenAt base f
    have hg := length_flattenAt (base + f.size) g
    have hfp := f.size_pos
    have hgp := g.size_pos
    simp only [flattenAt] at hk hu
    rw [List.getElem_append] at hu
    split at hu
    · rename_i h1
      rw [List.getElem_append] at hu
      split at hu
      · rename_i h2
        have := solution base f k (by omega) u hu
        omega
      · rename_i h2
        have := solution (base + f.size) g (k - (f.flattenAt base).length)
          (by simp only [List.length_append, hf, hg, List.length_singleton] at hk h1 ⊢; omega) u hu
        simp only [List.length_append, hf] at h1
        omega
    · rename_i h1
      simp only [List.length_append, hf, hg, List.length_singleton] at h1 hk
      have : k - (f.size + g.size) = 0 := by omega
      simp [this, Gate.refs] at hu
      rcases hu with rfl | rfl <;> omega
  | or f g, k, hk, u, hu => by
    have hf := length_flattenAt base f
    have hg := length_flattenAt (base + f.size) g
    have hfp := f.size_pos
    have hgp := g.size_pos
    simp only [flattenAt] at hk hu
    rw [List.getElem_append] at hu
    split at hu
    · rename_i h1
      rw [List.getElem_append] at hu
      split at hu
      · rename_i h2
        have := solution base f k (by omega) u hu
        omega
      · rename_i h2
        have := solution (base + f.size) g (k - (f.flattenAt base).length)
          (by simp only [List.length_append, hf, hg, List.length_singleton] at hk h1 ⊢; omega) u hu
        simp only [List.length_append, hf] at h1
        omega
    · rename_i h1
      simp only [List.length_append, hf, hg, List.length_singleton] at h1 hk
      have : k - (f.size + g.size) = 0 := by omega
      simp [this, Gate.refs] at hu
      rcases hu with rfl | rfl <;> omega
  | not f, k, hk, u, hu => by
    have hf := length_flattenAt base f
    have hfp := f.size_pos
    simp only [flattenAt] at hk hu
    rw [List.getElem_append] at hu
    split at hu
    · rename_i h1
      have := solution base f k (by omega) u hu
      omega
    · rename_i h1
      simp only [List.length_append, hf, List.length_singleton] at h1 hk
      have : k - f.size = 0 := by omega
      simp [this, Gate.refs] at hu
      omega
end MIPRE.SAT.Fml
