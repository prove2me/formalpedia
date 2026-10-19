-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryLinear.typedInsert_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:19:36.177281+00:00
-- url     : https://prove2.me/submissions/06dc1311-f10d-45df-a2bb-eaa94e471a34

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryBasis.lean (solution of MIPRE.LowDegree.BinaryLinear.typedInsert_mem_iff);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_binary_eq_zero_or_one

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
theorem vector_eq_zero_of_firstOne_ge (v : Fin n → ZMod 2)
    (h : ¬ firstOne (vectorBits v) < n) : v = 0 := by
  funext i
  rcases binary_eq_zero_or_one (v i) with hi | hi
  · exact hi
  · have hm : true ∈ vectorBits v := List.mem_ofFn.mpr ⟨i, by simp [bit, hi]⟩
    have hj := List.findIdx_lt_length_of_exists (xs := vectorBits v) (p := id)
      ⟨true, hm, rfl⟩
    exact False.elim (h (by simpa [firstOne, vectorBits] using hj))
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
/-- Adding a stored vector preserves membership in every subspace containing it. -/
theorem typedReduceStep_mem_iff (S : Submodule (ZMod 2) (Fin n → ZMod 2))
    (r : Row n t) (p : Pivot n t) (hp : p.2.1 ∈ S) :
    (typedReduceStep r p).1 ∈ S ↔ r.1 ∈ S := by
  unfold typedReduceStep
  split
  · constructor
    · intro h
      have hs := S.sub_mem h hp
      simpa using hs
    · intro h
      exact S.add_mem h hp
  · rfl
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
theorem typedReduce_mem_iff (S : Submodule (ZMod 2) (Fin n → ZMod 2))
    (b : List (Pivot n t)) (r : Row n t) (hb : ∀ p ∈ b, p.2.1 ∈ S) :
    (typedReduce b r).1 ∈ S ↔ r.1 ∈ S := by
  induction b generalizing r with
  | nil => rfl
  | cons p b ih =>
    change (typedReduce b (typedReduceStep r p)).1 ∈ S ↔ _
    rw [ih _ (fun q hq => hb q (by simp [hq])),
      typedReduceStep_mem_iff S r p (hb p (by simp))]
end
end MIPRE.LowDegree.BinaryLinear

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryLinear
variable {n t : ℕ}
theorem _root_.solution (S : Submodule (ZMod 2) (Fin n → ZMod 2))
    (b : List (Pivot n t)) (r : Row n t) :
    (∀ p ∈ typedInsert b r, p.2.1 ∈ S) ↔ (∀ p ∈ b, p.2.1 ∈ S) ∧ r.1 ∈ S := by
  unfold typedInsert
  dsimp only
  split
  · rename_i hj
    constructor
    · intro h
      have hb : ∀ p ∈ b, p.2.1 ∈ S := fun p hp => h p (List.mem_append_left _ hp)
      refine ⟨hb, (typedReduce_mem_iff S b r hb).mp ?_⟩
      exact h (⟨firstOne (vectorBits (typedReduce b r).1), hj⟩, typedReduce b r)
        (List.mem_append_right _ (List.mem_singleton_self _))
    · rintro ⟨hb, hr⟩ p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hb p hp
      · obtain rfl := List.mem_singleton.mp hp
        exact (typedReduce_mem_iff S b r hb).mpr hr
  · rename_i hn
    have hz := vector_eq_zero_of_firstOne_ge (typedReduce b r).1 hn
    constructor
    · intro hb
      refine ⟨hb, (typedReduce_mem_iff S b r hb).mp ?_⟩
      rw [hz]
      exact S.zero_mem
    · exact fun h => h.1
end MIPRE.LowDegree.BinaryLinear
