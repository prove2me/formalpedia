-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryLinear.groupComponents_primitive
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:30:27.174606+00:00
-- url     : https://prove2.me/submissions/4333712c-7012-4e69-a6b9-ff66ffe45a67

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryComponents.lean (solution of MIPRE.LowDegree.BinaryLinear.groupComponents_primitive);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_IsPivotBasis_append_reduced
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_IsPivotBasis_eq_zero_of_pivots_zero
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_binary_eq_zero_or_one
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_getD_vectorBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_typedBasis_span
import Theorems.Thm_MIPRE_LowDegree_ComponentFamily_split
import Theorems.Thm_MIPRE_LowDegree_decidesComponent_of_mem_span

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
variable {n t : ℕ}
/-- A row whose value is zero keeps its entire certificate unchanged. -/
theorem typedReduce_zero_value (b : List (Pivot n t)) (x : Fin t → ZMod 2) :
    typedReduce b (0, x) = (0, x) := by
  induction b with
  | nil => rfl
  | cons p b ih =>
    change typedReduce b (typedReduceStep (0, x) p) = _
    have hs : typedReduceStep (0, x) p = (0, x) := by simp [typedReduceStep]
    rw [hs, ih]
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
section
open Cost Cost.PolyTimeFun
variable {n t : ℕ}
/-- The projection fixes every vector already in the kernel. -/
theorem kernelMap_fixed {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (x : Fin n → ZMod 2) (hx : x ∈ A.mulVecLin.ker) : kernelMap A x = x := by
  rw [LinearMap.mem_ker] at hx
  rw [kernelMap_apply, show A.mulVec x = 0 from hx, typedReduce_zero_value]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
variable {n t : ℕ}
theorem kernelMap_range {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    (kernelMap A).range = A.mulVecLin.ker := by
  apply le_antisymm
  · rintro v ⟨x, rfl⟩
    exact kernelMap_mem_ker A x
  · intro x hx
    exact ⟨x, kernelMap_fixed A x hx⟩
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
variable {n t : ℕ}
/-- The images of the standard basis generate exactly the matrix kernel. -/
theorem kernel_generators_span {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    Submodule.span (ZMod 2) (Set.range (fun j : Fin n => kernelMap A (Pi.single j 1))) =
      A.mulVecLin.ker := by
  let K := LinearMap.toMatrix' (kernelMap A)
  have hK : K.mulVecLin = kernelMap A := by
    exact Matrix.toLin'_toMatrix' (kernelMap A)
  have hcols : K.col = fun j : Fin n => kernelMap A (Pi.single j 1) := by
    funext j i
    exact LinearMap.toMatrix'_apply (kernelMap A) i j
  rw [← hcols, ← Matrix.range_mulVecLin, hK, kernelMap_range]
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
/-- Every idempotent lies in the binary span of the computed generators. -/
theorem groupFixedGenerator_spans (k : ℕ) [NeZero k]
    (z : AddMonoidAlgebra (ZMod 2) (Fin k)) (hz : z * z = z) :
    z ∈ Submodule.span (ZMod 2) (Set.range (groupFixedGenerator k)) := by
  have hc := (groupFixedMatrix_ker k z).mpr hz
  rw [← kernel_generators_span] at hc
  have hm : z ∈ Submodule.map (groupCoordinates k).symm.toLinearMap
      (Submodule.span (ZMod 2) (Set.range (fun j : Fin k =>
        kernelMap (groupFixedMatrix k) (Pi.single j 1)))) :=
    Submodule.mem_map.mpr ⟨groupCoordinates k z, hc, (groupCoordinates k).symm_apply_apply z⟩
  rw [Submodule.map_span, ← Set.range_comp] at hm
  change z ∈ Submodule.span (ZMod 2) (Set.range (groupFixedGenerator k)) at hm
  exact hm
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree
noncomputable section
variable {R : Type*} [CommRing R] [DecidableEq R]
theorem mem_splitComponent (e b x : R) :
    x ∈ splitComponent e b ↔ (x = e * b ∨ x = e * (1 - b)) ∧ x ≠ 0 := by
  simp [splitComponent, and_comm]
end
end MIPRE.LowDegree

namespace MIPRE.LowDegree
noncomputable section
variable {R : Type*} [CommRing R] [DecidableEq R]
theorem splitComponent_factor {e b x : R} (hx : x ∈ splitComponent e b) :
    ∃ c, x = e * c := by
  rcases (mem_splitComponent e b x).mp hx with ⟨h | h, _⟩
  · exact ⟨b, h⟩
  · exact ⟨1 - b, h⟩
end
end MIPRE.LowDegree

namespace MIPRE.LowDegree
noncomputable section
variable {R : Type*} [CommRing R] [DecidableEq R]
theorem splitComponent_decides {e b x : R} (hb : b * b = b) (hx : x ∈ splitComponent e b) :
    DecidesComponent x b := by
  rcases (mem_splitComponent e b x).mp hx with ⟨rfl | rfl, _⟩
  · right
    rw [mul_assoc, hb]
  · left
    calc
      (e * (1 - b)) * b = e * (b - b * b) := by ring
      _ = 0 := by rw [hb, sub_self, mul_zero]
end
end MIPRE.LowDegree

namespace MIPRE.LowDegree
noncomputable section
variable {R : Type*} [CommRing R] [DecidableEq R]
theorem splitComponent_preserves {e b c x : R} (hc : DecidesComponent e c)
    (hx : x ∈ splitComponent e b) : DecidesComponent x c := by
  obtain ⟨d, rfl⟩ := splitComponent_factor hx
  have hm : (e * d) * c = (e * c) * d := by ring
  rcases hc with h | h
  · left
    rw [hm, h, zero_mul]
  · right
    rw [hm, h]
end
end MIPRE.LowDegree

namespace MIPRE.LowDegree
noncomputable section
variable {R : Type*} [CommRing R] [DecidableEq R]
theorem ComponentFamily.splitAll {l bs : List R} (hl : ComponentFamily l)
    (hb : ∀ b ∈ bs, b * b = b) : ComponentFamily (splitAllComponents l bs) := by
  induction bs generalizing l with
  | nil => exact hl
  | cons b bs ih =>
    exact ih (hl.split (hb b (by simp))) (fun c hc => hb c (by simp [hc]))
end
end MIPRE.LowDegree

namespace MIPRE.LowDegree
noncomputable section
variable {R : Type*} [CommRing R] [DecidableEq R]
theorem splitAllComponents_preserves {l bs : List R} {c : R}
    (hc : ∀ e ∈ l, DecidesComponent e c) :
    ∀ e ∈ splitAllComponents l bs, DecidesComponent e c := by
  induction bs generalizing l with
  | nil => exact hc
  | cons b bs ih =>
    apply ih
    intro x hx
    obtain ⟨e, he, hx⟩ := List.mem_flatMap.mp hx
    exact splitComponent_preserves (hc e he) hx
end
end MIPRE.LowDegree

namespace MIPRE.LowDegree
noncomputable section
variable {R : Type*} [CommRing R] [DecidableEq R]
theorem splitAllComponents_decides {l bs : List R}
    (hb : ∀ b ∈ bs, b * b = b) :
    ∀ e ∈ splitAllComponents l bs, ∀ b ∈ bs, DecidesComponent e b := by
  induction bs generalizing l with
  | nil => simp
  | cons c bs ih =>
    intro e he b hbmem
    rcases List.mem_cons.mp hbmem with hbc | hbmem
    · subst b
      apply splitAllComponents_preserves (l := splitComponents l c) (bs := bs) ?_ e he
      intro x hx
      obtain ⟨d, _, hx⟩ := List.mem_flatMap.mp hx
      exact splitComponent_decides (hb c (by simp)) hx
    · exact ih (fun b hb' => hb b (by simp [hb'])) e he b hbmem
end
end MIPRE.LowDegree

namespace MIPRE.LowDegree
noncomputable section
variable {R : Type*} [CommRing R] [DecidableEq R]
variable [Algebra (ZMod 2) R]
attribute [local instance] MIPRE.LowDegree.instFactPrimeOfNatNat_mIPRE
/-- Separating a spanning family of fixed vectors makes every remaining component primitive. -/
theorem splitAllComponents_primitive {l bs : List R} (hl : ComponentFamily l)
    (hb : ∀ b ∈ bs, b * b = b)
    (hspan : ∀ z : R, z * z = z → z ∈ Submodule.span (ZMod 2) {b | b ∈ bs}) :
    ∀ e ∈ splitAllComponents l bs, PrimitiveBinaryComponent e := by
  intro e he
  have hf := hl.splitAll hb
  refine ⟨hf.nonzero e he, hf.idempotent e he, fun z hz => ?_⟩
  exact decidesComponent_of_mem_span e bs (splitAllComponents_decides hb e he) z (hspan z hz)
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
theorem groupFixedFamily_spans (k : ℕ) [NeZero k]
    (z : AddMonoidAlgebra (ZMod 2) (Fin k)) (hz : z * z = z) :
    z ∈ Submodule.span (ZMod 2) {b | b ∈ groupFixedFamily k} := by
  have hs : {b | b ∈ groupFixedFamily k} = Set.range (groupFixedGenerator k) := by
    ext b
    simp [groupFixedFamily]
  rw [hs]
  exact groupFixedGenerator_spans k z hz
end
end MIPRE.LowDegree.BinaryLinear

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryLinear
open Cost
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE_2
theorem _root_.solution (k : ℕ) [NeZero k] :
    ∀ e ∈ groupComponents k, PrimitiveBinaryComponent e :=
  splitAllComponents_primitive (unitComponentFamily k) (groupFixedFamily_idempotent k)
    (groupFixedFamily_spans k)
end MIPRE.LowDegree.BinaryLinear
