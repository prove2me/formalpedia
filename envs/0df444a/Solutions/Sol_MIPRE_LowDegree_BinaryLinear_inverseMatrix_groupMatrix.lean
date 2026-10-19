-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryLinear.inverseMatrix_groupMatrix
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:25:05.121815+00:00
-- url     : https://prove2.me/submissions/bd912315-53dd-48b9-9530-2098f12ffece

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryCirculant.lean (solution of MIPRE.LowDegree.BinaryLinear.inverseMatrix_groupMatrix);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_IsPivotBasis_append_reduced
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_IsPivotBasis_eq_zero_of_pivots_zero
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_binary_eq_zero_or_one
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_coordinateRows_matrixBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_getD_vectorBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_insertRow_pivotBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_typedBasis_span
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_typedReduceStep_error
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_xorBits_vectorBits

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun Polynomial
/-- A raw XOR step is the corresponding operation on both typed vectors. -/
theorem reduceStep_rowBits {n t : ℕ} (r : Row n t) (p : Pivot n t) :
    reduceStep (rowBits r) (pivotBits p) = rowBits (typedReduceStep r p) := by
  unfold reduceStep pivotBits rowBits
  rw [getD_vectorBits]
  simp only [bit, decide_eq_true_eq, typedReduceStep]
  split_ifs
  · rw [xorBits_vectorBits, xorBits_vectorBits]
  · rfl
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun Polynomial
/-- The entire executable reduction agrees with typed binary elimination. -/
theorem reduceRows_rowBits {n t : ℕ} (b : List (Pivot n t)) (r : Row n t) :
    reduceRows (b.map pivotBits) (rowBits r) = rowBits (typedReduce b r) := by
  induction b generalizing r with
  | nil => rfl
  | cons p b ih =>
    change reduceRows (b.map pivotBits) (reduceStep (rowBits r) (pivotBits p)) = _
    rw [reduceStep_rowBits, ih]
    rfl
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
theorem fold_insertRow_pivotBits (rows : List (Row n t)) (b : List (Pivot n t)) :
    (rows.map rowBits).foldl insertRow (b.map pivotBits) =
      (rows.foldl typedInsert b).map pivotBits := by
  induction rows generalizing b with
  | nil => rfl
  | cons r rows ih =>
    simp only [List.map_cons, List.foldl_cons, insertRow_pivotBits, ih]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
/-- The actual ambient program constructs precisely the typed binary basis. -/
theorem basisRowsProg_correct (rows : List (Row n t)) :
    basisRowsProg (rows.map rowBits) = (typedBasis rows).map pivotBits :=
  fold_insertRow_pivotBits rows []
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
variable {n t : ℕ}
theorem typedReduce_error
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (b : List (Pivot n t)) (r : Row n t) (hb : ∀ p ∈ b, Represents L p.2) :
    (typedReduce b r).1 + L (typedReduce b r).2 = r.1 + L r.2 := by
  induction b generalizing r with
  | nil => rfl
  | cons p b ih =>
    change (typedReduce b (typedReduceStep r p)).1 + L (typedReduce b (typedReduceStep r p)).2 = _
    rw [ih _ (fun q hq => hb q (by simp [hq])), typedReduceStep_error L r p (hb p (by simp))]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
variable {n t : ℕ}
/-- Reducing a target with an initially zero certificate solves the original system. -/
theorem solve_certificate
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (b : List (Pivot n t)) (hb : IsPivotBasis b) (hrep : ∀ p ∈ b, Represents L p.2)
    (v : Fin n → ZMod 2) (hv : v ∈ pivotSpan b) :
    L (typedReduce b (v, 0)).2 = v := by
  have h := typedReduce_error L b (v, 0) hrep
  rw [hb.reduce_eq_zero (v, 0) hv, zero_add, map_zero, add_zero] at h
  exact h
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
variable {n t : ℕ}
/-- Correctness of the actual uniform binary solver on every target in the basis span. -/
theorem solveBitsProg_correct
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (b : List (Pivot n t)) (hb : IsPivotBasis b) (hrep : ∀ p ∈ b, Represents L p.2)
    (v : Fin n → ZMod 2) (hv : v ∈ pivotSpan b) :
    L (vectorValue t (solveBitsProg (unary t, b.map pivotBits, vectorBits v))) = v := by
  have hz : List.replicate t false = vectorBits (0 : Fin t → ZMod 2) := by
    simp [vectorBits, bit]
  change L (vectorValue t (reduceRows (b.map pivotBits)
    (vectorBits v, List.replicate (unary t).length false)).2) = v
  rw [length_unary, hz]
  change L (vectorValue t (reduceRows (b.map pivotBits) (rowBits (v, 0))).2) = v
  rw [reduceRows_rowBits]
  change L (vectorValue t (vectorBits (typedReduce b (v, 0)).2)) = v
  rw [vectorValue_vectorBits]
  exact solve_certificate L b hb hrep v hv
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
variable {n t : ℕ}
/-- The program solves any consistent binary linear system with supplied generator coordinates. -/
theorem basisSolveProg_correct
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (rows : List (Row n t)) (hr : ∀ r ∈ rows, Represents L r)
    (v : Fin n → ZMod 2) (hv : v ∈ rowSpan rows) :
    L (vectorValue t (basisSolveProg (unary t, rows.map rowBits, vectorBits v))) = v := by
  change L (vectorValue t (solveBitsProg (unary t, basisRowsProg (rows.map rowBits), vectorBits v))) = v
  rw [basisRowsProg_correct]
  apply solveBitsProg_correct L _ (typedBasis_isPivotBasis rows) (typedBasis_represents L rows hr) v
  rwa [typedBasis_span]
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
/-- A globally polynomial-time solver for every consistent binary matrix system. -/
theorem matrixSolveProg_correct {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (v : Fin m → ZMod 2)
    (hv : ∃ x, A.mulVec x = v) :
    A.mulVec (vectorValue n (matrixSolveProg (unary n, matrixBits A, vectorBits v))) = v := by
  change A.mulVecLin (vectorValue n (basisSolveProg
    (unary n, coordinateRows (transposeBits (unary n).length (matrixBits A)), vectorBits v))) = v
  rw [length_unary, coordinateRows_matrixBits]
  apply basisSolveProg_correct A.mulVecLin _ (columnRows_represents A) v
  rw [rowSpan_columnRows, LinearMap.mem_range]
  exact hv
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem matrixSolution_correct {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (v : Fin m → ZMod 2)
    (hv : ∃ x, A.mulVec x = v) : A.mulVec (matrixSolution A v) = v := by
  have h := matrixSolveProg_correct A v hv
  rwa [matrixSolveProg_encoding, vectorValue_vectorBits] at h
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
/-- For nonsingular matrices, the computed columns form a right inverse. -/
theorem mul_inverseMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (hA : Function.Surjective A.mulVec) : A * inverseMatrix A = 1 := by
  ext i j
  have h := congrFun (matrixSolution_correct A (Pi.single j 1) (hA _)) i
  change (A.mulVec (matrixSolution A (Pi.single j 1))) i = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) i j
  rw [h]
  simp [Pi.single_apply, Matrix.one_apply, eq_comm]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
/-- Over the finite binary field the computed right inverse is also a left inverse. -/
theorem inverseMatrix_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (hA : Function.Surjective A.mulVec) : inverseMatrix A * A = 1 :=
  mul_eq_one_comm.mp (mul_inverseMatrix A hA)
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
noncomputable section
open Cost
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
theorem groupMatrix_injective : Function.Injective (groupMatrix (G := G)) := by
  intro z w h
  apply AddMonoidAlgebra.coeff_injective
  ext g
  simpa [groupMatrix] using congrArg (fun A => A g 0) h
end
end MIPRE.LowDegree.BinaryLinear

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryLinear
open Cost
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
theorem _root_.solution {k : ℕ} [NeZero k]
    (z : AddMonoidAlgebra (ZMod 2) (Fin k))
    (hz : Function.Surjective (groupMatrix z).mulVec) :
    ∃ u : AddMonoidAlgebra (ZMod 2) (Fin k), z * u = 1 ∧
      inverseMatrix (groupMatrix z) = groupMatrix u := by
  haveI : Finite (AddMonoidAlgebra (ZMod 2) (Fin k)) :=
    Finite.of_injective AddMonoidAlgebra.coeff AddMonoidAlgebra.coeff_injective
  have hinj : Function.Injective (fun u => z * u) := by
    intro x y h
    apply groupMatrix_injective
    have hh := congrArg groupMatrix h
    rw [groupMatrix_mul, groupMatrix_mul] at hh
    have hh' := congrArg (fun A => inverseMatrix (groupMatrix z) * A) hh
    simpa only [← Matrix.mul_assoc, inverseMatrix_mul _ hz, Matrix.one_mul] using hh'
  obtain ⟨u, hu⟩ := (Finite.injective_iff_surjective.mp hinj) 1
  change z * u = 1 at hu
  refine ⟨u, hu, ?_⟩
  have hm : groupMatrix z * groupMatrix u = 1 := by
    rw [← groupMatrix_mul, hu]
    exact groupMatrixHom.map_one
  calc
    inverseMatrix (groupMatrix z) = inverseMatrix (groupMatrix z) *
        (groupMatrix z * groupMatrix u) := by rw [hm, Matrix.mul_one]
    _ = groupMatrix u := by rw [← Matrix.mul_assoc, inverseMatrix_mul _ hz, Matrix.one_mul]
end MIPRE.LowDegree.BinaryLinear
