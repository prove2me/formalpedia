-- Prove2me | solution 1 for MIPRE.Cost.Data.chunkPairs_eq_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:35:14.562787+00:00
-- url     : https://prove2.me/submissions/4175315e-bbc7-4e55-a75f-53c79cb0ac03

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/Prims.lean (solution of MIPRE.Cost.Data.chunkPairs_eq_ofFn);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Data
section
open Data
theorem chunkPairs_nil (s : ℕ) (hs : 0 < s) (y : List Data) : chunkPairs s hs [] y = [] := by
  rw [chunkPairs]
end
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
section
open Data
theorem chunkPairs_cons (s : ℕ) (hs : 0 < s) (h : Data) (l y : List Data) :
    chunkPairs s hs (h :: l) y =
      ((h :: l).take s, y.take s) :: chunkPairs s hs ((h :: l).drop s) (y.drop s) := by
  rw [chunkPairs]
end
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
section
open Data
theorem chunkPairs_of_ne_nil (s : ℕ) (hs : 0 < s) {l : List Data} (hl : l ≠ []) (y : List Data) :
    chunkPairs s hs l y = (l.take s, y.take s) :: chunkPairs s hs (l.drop s) (y.drop s) := by
  cases l with
  | nil => exact absurd rfl hl
  | cons h l => exact chunkPairs_cons s hs h l y
end
end MIPRE.Cost.Data

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Data
open Data
theorem _root_.solution (s : ℕ) (hs : 0 < s) : ∀ (k : ℕ) (l y : List Data),
    l.length = k * s → chunkPairs s hs l y = List.ofFn fun i : Fin k => (chunk s i l, chunk s i y)
  | 0, l, y, hl => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst this
    simp [chunkPairs_nil]
  | k + 1, l, y, hl => by
    have hne : l ≠ [] := by
      intro h; subst h; simp at hl; nlinarith
    rw [chunkPairs_of_ne_nil s hs hne, List.ofFn_succ]
    have hlen : (l.drop s).length = k * s := by
      rw [List.length_drop, hl]; rw [Nat.succ_mul]; omega
    rw [solution s hs k (l.drop s) (y.drop s) hlen]
    congr 1
    · simp [chunk]
    · congr 1
      funext i
      simp only [chunk, Fin.val_succ, List.drop_drop]
      congr 3 <;> ring
end MIPRE.Cost.Data
