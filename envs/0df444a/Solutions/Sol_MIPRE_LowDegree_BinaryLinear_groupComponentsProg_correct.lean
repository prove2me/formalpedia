-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryLinear.groupComponentsProg_correct
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:52:40.369985+00:00
-- url     : https://prove2.me/submissions/4dbee8c6-75b7-4c30-becc-b9c2c4d1e39f

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryComponentsProg.lean (solution of MIPRE.LowDegree.BinaryLinear.groupComponentsProg_correct);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.ToLin
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixInverse
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySquareRoot
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculant
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra_B
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg_B
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_IsPivotBasis_append_reduced
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_IsPivotBasis_eq_zero_of_pivots_zero
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_binary_eq_zero_or_one
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_circulantBitsProg_correct
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_getD_vectorBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_identityBits_eq_matrixBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_kernelGeneratorsProg_encoding
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_transposeBits_matrixBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_typedBasis_span
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_xorBits_vectorBits
import Theorems.Thm_MIPRE_LowDegree_ComponentFamily_linearIndependent
import Theorems.Thm_MIPRE_LowDegree_ComponentFamily_split

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem ofBool_injective : Function.Injective (ofBool : Bool → ZMod 2) := by
  intro a b h
  have := congrArg bit h
  simpa using this
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem ofBool_xor (a b : Bool) :
    (ofBool (a ^^ b) : ZMod 2) = ofBool a + ofBool b := by
  cases a <;> cases b <;> decide
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem ofBool_and (a b : Bool) :
    (ofBool (a && b) : ZMod 2) = ofBool a * ofBool b := by
  cases a <;> cases b <;> decide
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem ofBool_fold_dotStep (l : List (Bool × Bool)) (b : Bool) :
    (ofBool (l.foldl dotStep b) : ZMod 2) =
      ofBool b + (l.map (fun p => (ofBool p.1 : ZMod 2) * ofBool p.2)).sum := by
  induction l generalizing b with
  | nil => simp
  | cons p l ih =>
    rw [List.foldl_cons, ih]
    simp only [dotStep, ofBool_xor, ofBool_and, List.map_cons, List.sum_cons]
    ring
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem ofBool_dotBits (a b : BitStr) :
    (ofBool (dotBits a b) : ZMod 2) =
      ((a.zip b).map (fun p => (ofBool p.1 : ZMod 2) * ofBool p.2)).sum := by
  rw [dotBits, ofBool_fold_dotStep]
  simp [ofBool]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem zip_vectorBits {n : ℕ} (v w : Fin n → ZMod 2) :
    (vectorBits v).zip (vectorBits w) = List.ofFn (fun i => (bit (v i), bit (w i))) := by
  apply List.ext_getElem
  · simp [vectorBits]
  · intro i hi hj
    simp [vectorBits]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
/-- The raw parity circuit computes the exact binary dot product. -/
theorem dotBits_vectorBits {n : ℕ} (v w : Fin n → ZMod 2) :
    dotBits (vectorBits v) (vectorBits w) = bit (∑ i, v i * w i) := by
  apply ofBool_injective
  rw [ofBool_dotBits, zip_vectorBits, ofBool_bit]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, ofBool_bit]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
/-- Executable matrix application agrees with the usual binary matrix-vector product. -/
theorem applyBits_matrixBits {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (v : Fin n → ZMod 2) :
    applyBits (matrixBits A) (vectorBits v) = vectorBits (A.mulVec v) := by
  simp only [applyBits, matrixBits, List.map_ofFn, vectorBits]
  apply congrArg List.ofFn
  funext i
  exact dotBits_vectorBits (A i) v
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun Polynomial
theorem represents_typedReduceStep {n t : ℕ}
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (r : Row n t) (p : Pivot n t) (hr : Represents L r) (hp : Represents L p.2) :
    Represents L (typedReduceStep r p) := by
  unfold typedReduceStep
  split
  · change L (r.2 + p.2.2) = r.1 + p.2.1
    rw [map_add, hr, hp]
  · exact hr
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun Polynomial
/-- Reduction preserves the coefficient certificate in the original family. -/
theorem represents_typedReduce {n t : ℕ}
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (b : List (Pivot n t)) (r : Row n t) (hr : Represents L r)
    (hb : ∀ p ∈ b, Represents L p.2) : Represents L (typedReduce b r) := by
  induction b generalizing r with
  | nil => exact hr
  | cons p b ih =>
    exact ih _ (represents_typedReduceStep L r p hr (hb p (by simp)))
      (fun q hq => hb q (by simp [hq]))
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun Polynomial
theorem firstOne_getD (v : BitStr) (h : firstOne v < v.length) :
    v.getD (firstOne v) false = true := by
  have hbit := List.findIdx_getElem (xs := v) (p := id) (w := h)
  change v[firstOne v]?.getD false = true
  rw [List.getElem?_eq_getElem h]
  exact hbit
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE
theorem typedReduceStep_pivot_zero (r : Row n t) (p : Pivot n t)
    (hp : p.2.1 p.1 = 1) : (typedReduceStep r p).1 p.1 = 0 := by
  rcases binary_eq_zero_or_one (r.1 p.1) with h | h
  · simp [typedReduceStep, h]
  · simp only [typedReduceStep, h, if_true, Pi.add_apply, hp]
    decide
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE
theorem typedReduceStep_preserves_zero (r : Row n t) (p : Pivot n t) (j : Fin n)
    (hr : r.1 j = 0) (hp : p.2.1 j = 0) : (typedReduceStep r p).1 j = 0 := by
  unfold typedReduceStep
  split <;> simp [hr, hp]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE
theorem typedReduce_preserves_zero (b : List (Pivot n t)) (r : Row n t) (j : Fin n)
    (hr : r.1 j = 0) (hb : ∀ p ∈ b, p.2.1 j = 0) : (typedReduce b r).1 j = 0 := by
  induction b generalizing r with
  | nil => exact hr
  | cons p b ih =>
    exact ih _ (typedReduceStep_preserves_zero r p j hr (hb p (by simp)))
      (fun q hq => hb q (by simp [hq]))
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE
/-- Reducing against a triangular basis zeros all of its pivot coordinates. -/
theorem typedReduce_pivots_zero (b : List (Pivot n t)) (hb : IsPivotBasis b)
    (r : Row n t) : ∀ p ∈ b, (typedReduce b r).1 p.1 = 0 := by
  induction b generalizing r with
  | nil => simp
  | cons p b ih =>
    intro q hq
    rcases List.mem_cons.mp hq with hqp | hq
    · subst q
      exact typedReduce_preserves_zero b (typedReduceStep r p) p.1
        (typedReduceStep_pivot_zero r p hb.1) hb.2.1
    · exact ih hb.2.2 (typedReduceStep r p) q hq
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
theorem firstOne_vectorBits_one (v : Fin n → ZMod 2)
    (h : firstOne (vectorBits v) < n) : v ⟨firstOne (vectorBits v), h⟩ = 1 := by
  have hh := firstOne_getD (vectorBits v) (by simpa [vectorBits] using h)
  change (vectorBits v).getD (⟨firstOne (vectorBits v), h⟩ : Fin n) false = true at hh
  rw [getD_vectorBits] at hh
  simpa [bit] using hh
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
/-- Insertion maintains the triangular pivot invariant. -/
theorem IsPivotBasis.typedInsert {b : List (Pivot n t)} (hb : IsPivotBasis b) (r : Row n t) :
    IsPivotBasis (typedInsert b r) := by
  unfold MIPRE.LowDegree.BinaryLinear.typedInsert
  dsimp only
  split
  · rename_i h
    exact hb.append_reduced r _ (firstOne_vectorBits_one _ h)
  · exact hb
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
theorem fold_typedInsert_isPivotBasis (rows : List (Row n t)) (b : List (Pivot n t))
    (hb : IsPivotBasis b) : IsPivotBasis (rows.foldl typedInsert b) := by
  induction rows generalizing b with
  | nil => exact hb
  | cons r rows ih => exact ih _ (hb.typedInsert r)
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
theorem typedBasis_isPivotBasis (rows : List (Row n t)) : IsPivotBasis (typedBasis rows) :=
  fold_typedInsert_isPivotBasis rows [] trivial
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

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
variable {n t : ℕ}
/-- A member of the basis span reduces to zero. -/
theorem IsPivotBasis.reduce_eq_zero {b : List (Pivot n t)} (hb : IsPivotBasis b)
    (r : Row n t) (hr : r.1 ∈ pivotSpan b) : (typedReduce b r).1 = 0 := by
  apply hb.eq_zero_of_pivots_zero _ _ (typedReduce_pivots_zero b hb r)
  apply (typedReduce_mem_iff (pivotSpan b) b r _).mpr hr
  intro p hp
  exact Submodule.subset_span ⟨p, hp, rfl⟩
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
variable {n t : ℕ}
theorem represents_typedInsert
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (b : List (Pivot n t)) (r : Row n t)
    (hb : ∀ p ∈ b, Represents L p.2) (hr : Represents L r) :
    ∀ p ∈ typedInsert b r, Represents L p.2 := by
  unfold typedInsert
  dsimp only
  split
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hb p hp
    · obtain rfl := List.mem_singleton.mp hp
      exact represents_typedReduce L b r hr hb
  · exact hb
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
variable {n t : ℕ}
theorem represents_fold_typedInsert
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (rows : List (Row n t)) (b : List (Pivot n t))
    (hb : ∀ p ∈ b, Represents L p.2) (hr : ∀ r ∈ rows, Represents L r) :
    ∀ p ∈ rows.foldl typedInsert b, Represents L p.2 := by
  induction rows generalizing b with
  | nil => exact hb
  | cons r rows ih =>
    exact ih _ (represents_typedInsert L b r hb (hr r (by simp)))
      (fun s hs => hr s (by simp [hs]))
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
variable {n t : ℕ}
/-- Every constructed basis row retains its expression in the original generating family. -/
theorem typedBasis_represents
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (rows : List (Row n t)) (hr : ∀ r ∈ rows, Represents L r) :
    ∀ p ∈ typedBasis rows, Represents L p.2 :=
  represents_fold_typedInsert L rows [] (by simp) hr
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem unitBits_eq_vectorBits {n : ℕ} (j : Fin n) :
    unitBits n j = vectorBits (Pi.single j 1 : Fin n → ZMod 2) := by
  apply List.ext_getElem
  · simp [unitBits, vectorBits]
  · intro i hi hj
    simp only [unitBits, vectorBits, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    by_cases he : i = j
    · simp [bit, Pi.single_apply, Fin.ext_iff, he]
    · simp [bit, Pi.single_apply, Fin.ext_iff, he]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem columnRows_represents {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    ∀ r ∈ columnRows A, Represents A.mulVecLin r := by
  intro r hr
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
  exact Matrix.mulVec_single_one A j
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem rowSpan_columnRows {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    rowSpan (columnRows A) = A.mulVecLin.range := by
  rw [Matrix.range_mulVecLin]
  unfold rowSpan
  congr 1
  ext v
  simp only [Set.mem_setOf_eq, columnRows, List.mem_ofFn, Set.mem_range]
  constructor
  · rintro ⟨r, ⟨j, rfl⟩, hr⟩
    exact ⟨j, hr⟩
  · rintro ⟨j, hj⟩
    exact ⟨(A.col j, Pi.single j 1), ⟨j, rfl⟩, hj⟩
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem addMatrixBitsProg_correct {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) (ZMod 2)) :
    addMatrixBitsProg (matrixBits A, matrixBits B) = matrixBits (A + B) := by
  change ((matrixBits A).zip (matrixBits B)).map (fun p => BinaryPolynomial.xorBits p.1 p.2) = _
  apply List.ext_getElem
  · simp [matrixBits]
  · intro i hi hj
    simp only [matrixBits, List.getElem_map, List.getElem_zip, List.getElem_ofFn]
    exact xorBits_vectorBits _ _
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
variable {n t : ℕ}
theorem kernelMap_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (x : Fin n → ZMod 2) :
    kernelMap A x = (typedReduce (typedBasis (columnRows A)) (A.mulVec x, x)).2 := by
  simp [kernelMap]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
variable {n t : ℕ}
/-- Every output of the computed projection is in the matrix kernel. -/
theorem kernelMap_mem_ker {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (x : Fin n → ZMod 2) : kernelMap A x ∈ A.mulVecLin.ker := by
  have hp := typedBasis_represents A.mulVecLin (columnRows A) (columnRows_represents A)
  have hr : Represents A.mulVecLin (A.mulVec x, x) := rfl
  have hrel := represents_typedReduce A.mulVecLin (typedBasis (columnRows A))
    (A.mulVec x, x) hr hp
  have hz := (typedBasis_isPivotBasis (columnRows A)).reduce_eq_zero (A.mulVec x, x) (by
    rw [typedBasis_span, rowSpan_columnRows]
    exact ⟨x, rfl⟩)
  rw [LinearMap.mem_ker, kernelMap_apply]
  exact hrel.trans hz
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
noncomputable section
open Cost Cost.PolyTimeFun
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE_1
instance groupAlgebraCharP (k : ℕ) [NeZero k] :
    CharP (AddMonoidAlgebra (ZMod 2) (Fin k)) 2 :=
  charP_of_injective_algebraMap' (ZMod 2) 2
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
noncomputable section
open Cost Cost.PolyTimeFun
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE_1
theorem groupMulBitsProg_correct {k : ℕ} [NeZero k]
    (z w : AddMonoidAlgebra (ZMod 2) (Fin k)) :
    groupMulBitsProg (vectorBits (groupCoordinates k z), vectorBits (groupCoordinates k w)) =
      vectorBits (groupCoordinates k (z * w)) := by
  change applyBits (circulantBitsProg (vectorBits (groupCoordinates k z)))
    (vectorBits (groupCoordinates k w)) = _
  rw [circulantBitsProg_correct, applyBits_matrixBits]
  congr 1
  funext i
  rw [groupCoordinates_apply, AddMonoidAlgebra.coeff_mul_apply_right,
    Finsupp.sum_fintype _ _ (by intro j; simp)]
  simp only [Matrix.mulVec, dotProduct, Matrix.circulant_apply, groupCoordinates_apply,
    sub_eq_add_neg]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
noncomputable section
open Cost Cost.PolyTimeFun
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE_1
theorem groupSquareMatrixProg_correct (k : ℕ) [NeZero k] :
    groupSquareMatrixProg (unary k) = matrixBits (groupSquareMatrix k) := by
  have hc : (identityBits k).map (fun v => groupMulBitsProg (v, v)) =
      matrixBits (groupSquareMatrix k).transpose := by
    rw [identityBits_eq_matrixBits]
    simp only [matrixBits, List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    have hj : (1 : Matrix (Fin k) (Fin k) (ZMod 2)) j = Pi.single j 1 := by
      funext i
      simp [Pi.single_apply, Matrix.one_apply, eq_comm]
    change groupMulBitsProg (vectorBits ((1 : Matrix (Fin k) (Fin k) (ZMod 2)) j),
      vectorBits ((1 : Matrix (Fin k) (Fin k) (ZMod 2)) j)) = _
    rw [hj, ← groupCoordinates_finGroupOfVector (Pi.single j 1), groupMulBitsProg_correct]
    congr 1
    funext i
    change groupCoordinates k (finGroupOfVector (Pi.single j 1) *
      finGroupOfVector (Pi.single j 1)) i = (LinearMap.toMatrix' (groupSquareCoordinates k)) i j
    rw [LinearMap.toMatrix'_apply]
    simp [groupSquareCoordinates]
  change transposeBits (unary k).length ((identityBits (unary k).length).map
    (fun v => groupMulBitsProg (v, v))) = _
  rw [length_unary, hc, transposeBits_matrixBits, Matrix.transpose_transpose]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
noncomputable section
open Cost Cost.PolyTimeFun
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE_1
theorem groupFixedMatrix_ker (k : ℕ) [NeZero k]
    (z : AddMonoidAlgebra (ZMod 2) (Fin k)) :
    groupCoordinates k z ∈ (groupFixedMatrix k).mulVecLin.ker ↔ z * z = z := by
  rw [LinearMap.mem_ker]
  change (groupSquareMatrix k + 1).mulVec (groupCoordinates k z) = 0 ↔ _
  rw [Matrix.add_mulVec, Matrix.one_mulVec]
  have hs : (groupSquareMatrix k).mulVec (groupCoordinates k z) = groupCoordinates k (z * z) := by
    change (LinearMap.toMatrix' (groupSquareCoordinates k)).mulVec _ = _
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix', groupSquareCoordinates_apply]
  rw [hs, ← map_add, ← (groupCoordinates k).map_zero, (groupCoordinates k).injective.eq_iff]
  exact CharTwo.add_eq_zero
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
noncomputable section
open Cost Cost.PolyTimeFun
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE_1
theorem groupFixedMatrixProg_correct (k : ℕ) [NeZero k] :
    groupFixedMatrixProg (unary k) = matrixBits (groupFixedMatrix k) := by
  change addMatrixBitsProg (groupSquareMatrixProg (unary k), identityBits (unary k).length) = _
  rw [length_unary, groupSquareMatrixProg_correct, identityBits_eq_matrixBits,
    addMatrixBitsProg_correct]
  rfl
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
noncomputable section
open Cost Cost.PolyTimeFun
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE_1
theorem groupFixedGenerator_idempotent (k : ℕ) [NeZero k] (j : Fin k) :
    groupFixedGenerator k j * groupFixedGenerator k j = groupFixedGenerator k j := by
  apply (groupFixedMatrix_ker k _).mp
  rw [groupFixedGenerator, LinearEquiv.apply_symm_apply]
  exact kernelMap_mem_ker _ _
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
noncomputable section
open Cost Cost.PolyTimeFun
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE_1
/-- Exact encoding of the computed fixed-space generators; no linear combinations are enumerated. -/
theorem groupFixedGeneratorsProg_correct (k : ℕ) [NeZero k] :
    groupFixedGeneratorsProg (unary k) =
      List.ofFn (fun j => vectorBits (groupCoordinates k (groupFixedGenerator k j))) := by
  change kernelGeneratorsProg (unary k, groupFixedMatrixProg (unary k)) = _
  rw [groupFixedMatrixProg_correct, kernelGeneratorsProg_encoding]
  apply congrArg List.ofFn
  funext j
  rw [groupFixedGenerator, LinearEquiv.apply_symm_apply]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree
noncomputable section
variable {R : Type*} [CommRing R] [DecidableEq R]
variable [Algebra (ZMod 2) R]
attribute [local instance] MIPRE.LowDegree.instFactPrimeOfNatNat_mIPRE
/-- Thus refinement can retain at most the ambient vector-space dimension. -/
theorem ComponentFamily.length_le_finrank [Module.Finite (ZMod 2) R]
    {l : List R} (hl : ComponentFamily l) : l.length ≤ Module.finrank (ZMod 2) R := by
  simpa using hl.linearIndependent.fintype_card_le_finrank
end
end MIPRE.LowDegree

namespace MIPRE.LowDegree.BinaryLinear
noncomputable section
open Cost
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE_2
theorem groupFixedFamily_idempotent (k : ℕ) [NeZero k] :
    ∀ b ∈ groupFixedFamily k, b * b = b := by
  intro b hb
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
  exact groupFixedGenerator_idempotent k j
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
noncomputable section
open Cost
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE_2
theorem groupAlgebra_finrank (k : ℕ) :
    Module.finrank (ZMod 2) (AddMonoidAlgebra (ZMod 2) (Fin k)) = k := by
  rw [(groupCoordinates k).finrank_eq]
  simp
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
noncomputable section
open Cost
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE_2
theorem vectorBits_injective {k : ℕ} : Function.Injective (vectorBits (n := k)) := by
  intro v w h
  have he := congrArg (vectorValue k) h
  simpa using he
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
noncomputable section
open Cost
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE_2
theorem nonzeroRow_groupBits (k : ℕ)
    (z : AddMonoidAlgebra (ZMod 2) (Fin k)) :
    nonzeroRow (vectorBits (groupCoordinates k z)) = decide (z ≠ 0) := by
  unfold nonzeroRow
  rw [zeroRow_vectorBits, ← (groupCoordinates k).map_zero]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact not_congr ((vectorBits_injective (k := k)).eq_iff.trans
    (groupCoordinates k).injective.eq_iff)
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
noncomputable section
open Cost
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE_2
theorem splitBits_encoding {k : ℕ} [NeZero k]
    (e b : AddMonoidAlgebra (ZMod 2) (Fin k)) :
    splitBits (vectorBits (groupCoordinates k e)) (vectorBits (groupCoordinates k b)) =
      (splitComponent e b).map (fun z => vectorBits (groupCoordinates k z)) := by
  unfold splitBits
  rw [groupMulBitsProg_correct]
  dsimp only
  rw [xorBits_vectorBits, ← map_add]
  have hsecond : e + e * b = e * (1 - b) := by
    rw [CharTwo.sub_eq_add, mul_add, mul_one]
  rw [hsecond]
  unfold splitComponent
  by_cases h₁ : e * b = 0 <;> by_cases h₂ : e * (1 - b) = 0 <;>
    simp [List.filter_cons, nonzeroRow_groupBits, h₁, h₂]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
noncomputable section
open Cost
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE_2
theorem splitBitsCapped_encoding {k : ℕ} [NeZero k]
    (l : List (AddMonoidAlgebra (ZMod 2) (Fin k))) (hl : ComponentFamily l)
    (b : AddMonoidAlgebra (ZMod 2) (Fin k)) (hb : b * b = b) :
    splitBitsCapped (unary k) (l.map (fun z => vectorBits (groupCoordinates k z)))
      (vectorBits (groupCoordinates k b)) =
      (splitComponents l b).map (fun z => vectorBits (groupCoordinates k z)) := by
  have he : (l.map (fun z => vectorBits (groupCoordinates k z))).flatMap
      (fun e => splitBits e (vectorBits (groupCoordinates k b))) =
      (splitComponents l b).map (fun z => vectorBits (groupCoordinates k z)) := by
    simp only [List.flatMap_map, splitBits_encoding, splitComponents, List.map_flatMap]
  unfold splitBitsCapped
  rw [he, length_unary, List.take_of_length_le]
  haveI : Module.Finite (ZMod 2) (AddMonoidAlgebra (ZMod 2) (Fin k)) :=
    Module.Finite.equiv (groupCoordinates k).symm
  simpa only [List.length_map, groupAlgebra_finrank] using (hl.split hb).length_le_finrank
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
noncomputable section
open Cost Cost.PolyTimeFun Polynomial
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE_3
theorem fold_componentStep_encoding {k : ℕ} [NeZero k]
    (bs l : List (AddMonoidAlgebra (ZMod 2) (Fin k)))
    (hl : ComponentFamily l) (hb : ∀ b ∈ bs, b * b = b) :
    (bs.map (fun z => vectorBits (groupCoordinates k z))).foldl componentStep
      (unary k, l.map (fun z => vectorBits (groupCoordinates k z))) =
    (unary k, (splitAllComponents l bs).map (fun z => vectorBits (groupCoordinates k z))) := by
  induction bs generalizing l with
  | nil => rfl
  | cons b bs ih =>
    have hbb := hb b (by simp)
    rw [List.map_cons, List.foldl_cons]
    change (bs.map _).foldl componentStep (unary k, splitBitsCapped _ _ _) = _
    rw [splitBitsCapped_encoding l hl b hbb, ih _ (hl.split hbb)
      (fun x hx => hb x (by simp [hx]))]
    rfl
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
noncomputable section
open Cost Cost.PolyTimeFun Polynomial
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE_3
theorem unitBits_group_one (k : ℕ) [NeZero k] :
    unitBits k 0 = vectorBits (groupCoordinates k (1 : AddMonoidAlgebra (ZMod 2) (Fin k))) := by
  rw [show unitBits k 0 = vectorBits (Pi.single (0 : Fin k) 1) from
    by simpa using unitBits_eq_vectorBits (0 : Fin k)]
  congr 1
  funext i
  change Pi.single (0 : Fin k) 1 i = (AddMonoidAlgebra.single 0 1).coeff i
  simp [Pi.single_apply, Finsupp.single_apply, eq_comm]
end
end MIPRE.LowDegree.BinaryLinear

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryLinear
open Cost Cost.PolyTimeFun Polynomial
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE_3
theorem _root_.solution (k : ℕ) [NeZero k] :
    groupComponentsProg (unary k) =
      (groupComponents k).map (fun z => vectorBits (groupCoordinates k z)) := by
  have hg : groupFixedGeneratorsProg (unary k) =
      (groupFixedFamily k).map (fun z => vectorBits (groupCoordinates k z)) := by
    rw [groupFixedGeneratorsProg_correct]
    simp only [groupFixedFamily, List.map_ofFn]
    rfl
  have hu : ComponentFamily ([1] : List (AddMonoidAlgebra (ZMod 2) (Fin k))) := by
    constructor <;> simp
  change ((groupFixedGeneratorsProg (unary k)).foldl componentStep
    (unary k, [unitBits (unary k).length 0])).2 = _
  rw [hg, length_unary, unitBits_group_one]
  change ((groupFixedFamily k |>.map (fun z => vectorBits (groupCoordinates k z))).foldl
    componentStep (unary k, ([1] : List (AddMonoidAlgebra (ZMod 2) (Fin k))).map
      (fun z => vectorBits (groupCoordinates k z)))).2 = _
  rw [fold_componentStep_encoding _ _ hu (groupFixedFamily_idempotent k)]
  rfl
end MIPRE.LowDegree.BinaryLinear
