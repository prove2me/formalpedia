-- Prove2me | solution 1 for MIPRE.SAT.Fml.eval_toCircuit
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:52:33.320729+00:00
-- url     : https://prove2.me/submissions/38ac7f94-fbc2-47a3-aff5-6a99b48cc14c

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Formula.lean (solution of MIPRE.SAT.Fml.eval_toCircuit);
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
import Theorems.Thm_MIPRE_SAT_Fml_valueAt_flattenAt

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.Fml
open Cost
theorem _root_.solution (n : ℕ) (f : Fml) (x : ℕ → Bool) : (f.toCircuit n).eval x = f.eval x := by
  have h : (Circuit.mk n (f.flattenAt 0)).valueAt x (0 + f.size - 1) = f.eval x := by
    have := valueAt_flattenAt n x f [] []
    rwa [List.append_nil] at this
  rw [Nat.zero_add] at h
  unfold Circuit.eval
  have hne : f.flattenAt 0 ≠ [] := by
    intro h'
    have h1 := length_flattenAt 0 f
    rw [h'] at h1
    have h2 := f.size_pos
    simp only [List.length_nil] at h1
    omega
  simp only [toCircuit, hne, ↓reduceIte, length_flattenAt]
  exact h
end MIPRE.SAT.Fml
