-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryLinear.typedBasis_span
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:21:04.313201+00:00
-- url     : https://prove2.me/submissions/b501617c-54b2-4f4e-b369-6d293a4b53f0

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryBasis.lean (solution of MIPRE.LowDegree.BinaryLinear.typedBasis_span);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Linarith
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
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_typedInsert_mem_iff

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
theorem fold_typedInsert_mem_iff (S : Submodule (ZMod 2) (Fin n → ZMod 2))
    (rows : List (Row n t)) (b : List (Pivot n t)) :
    (∀ p ∈ rows.foldl typedInsert b, p.2.1 ∈ S) ↔
      (∀ p ∈ b, p.2.1 ∈ S) ∧ (∀ r ∈ rows, r.1 ∈ S) := by
  induction rows generalizing b with
  | nil => simp
  | cons r rows ih =>
    rw [List.foldl_cons, ih, typedInsert_mem_iff]
    simp only [List.forall_mem_cons]
    tauto
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
/-- Output and input generate exactly the same binary subspace. -/
theorem typedBasis_mem_iff (S : Submodule (ZMod 2) (Fin n → ZMod 2))
    (rows : List (Row n t)) :
    (∀ p ∈ typedBasis rows, p.2.1 ∈ S) ↔ ∀ r ∈ rows, r.1 ∈ S := by
  simpa [typedBasis] using fold_typedInsert_mem_iff S rows []
end
end MIPRE.LowDegree.BinaryLinear

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryLinear
variable {n t : ℕ}
theorem _root_.solution (rows : List (Row n t)) : pivotSpan (typedBasis rows) = rowSpan rows := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨p, hp, rfl⟩
    apply (typedBasis_mem_iff (rowSpan rows) rows).mpr _ p hp
    intro r hr
    exact Submodule.subset_span ⟨r, hr, rfl⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨r, hr, rfl⟩
    apply (typedBasis_mem_iff (pivotSpan (typedBasis rows)) rows).mp _ r hr
    intro p hp
    exact Submodule.subset_span ⟨p, hp, rfl⟩
end MIPRE.LowDegree.BinaryLinear
