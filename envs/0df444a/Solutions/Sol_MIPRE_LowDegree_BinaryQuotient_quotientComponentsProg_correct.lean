-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryQuotient.quotientComponentsProg_correct
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:10:26.255663+00:00
-- url     : https://prove2.me/submissions/037f6995-ef90-4823-81c6-e763102deb6f

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryQuotientComponents.lean (solution of MIPRE.LowDegree.BinaryQuotient.quotientComponentsProg_correct);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Div
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
import Mathlib.RingTheory.AdjoinRoot
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotient
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDivision
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientComponents
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_IsPivotBasis_append_reduced
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_IsPivotBasis_eq_zero_of_pivots_zero
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_binary_eq_zero_or_one
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_getD_vectorBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_kernelGeneratorsProg_encoding
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_typedBasis_span
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_xorBits_vectorBits
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_oneBits
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_fixedMatrix_ker
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_frobeniusMatrixProg_correct
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_splitBits_encoding
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_toBits_ofBits
import Theorems.Thm_MIPRE_LowDegree_ComponentFamily_linearIndependent
import Theorems.Thm_MIPRE_LowDegree_ComponentFamily_split

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost BinaryPolynomial
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
include hf in
/-- Equality in any monic quotient is faithful on fixed-width coefficient lists. -/
theorem evalBits_eq_iff (a b : BitStr)
    (ha : a.length = f.natDegree) (hb : b.length = f.natDegree) :
    evalBits (AdjoinRoot.root f) a = evalBits (AdjoinRoot.root f) b ↔ a = b := by
  rw [← ofBits_eq_evalBits f hf a ha, ← ofBits_eq_evalBits f hf b hb]
  constructor
  · intro h
    have he := congrArg (toBits f hf) h
    simpa only [toBits_ofBits f hf a ha, toBits_ofBits f hf b hb] using he
  · rintro rfl
    rfl
end
end MIPRE.LowDegree.BinaryQuotient

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
theorem identityBits_eq_matrixBits (n : ℕ) :
    identityBits n = matrixBits (1 : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  apply List.ext_getElem
  · simp [identityBits, matrixBits]
  · intro i hi hj
    have hin : i < n := by simpa [identityBits] using hi
    simp only [identityBits, matrixBits, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [unitBits_eq_vectorBits (⟨i, hin⟩ : Fin n)]
    congr 1
    funext j
    simp [Pi.single_apply, Matrix.one_apply, eq_comm]
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

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost BinaryPolynomial BinaryLinear
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
/-- Quotient bit encodings agree with the generic binary linear coordinates. -/
theorem toBits_eq_vectorBits (x : AdjoinRoot f) :
    toBits f hf x = vectorBits (coordinateEquiv f hf x) := rfl
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost BinaryPolynomial BinaryLinear
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
/-- The fixed-space equation is generated uniformly from the supplied modulus. -/
theorem fixedMatrixProg_correct (p : BitStr)
    (hp : p.length = f.natDegree) (hpoly : f = polyOfBits (p ++ [true])) :
    fixedMatrixProg p = matrixBits (fixedMatrix f hf) := by
  simp only [fixedMatrixProg, Cost.PolyTimeFun.comp_apply,
    Cost.PolyTimeFun.pair_apply, Cost.PolyTimeFun.length_apply]
  change addMatrixBitsProg (frobeniusMatrixProg p, identityBits (unary p.length).length) = _
  rw [length_unary, hp, frobeniusMatrixProg_correct f hf p hp hpoly,
    identityBits_eq_matrixBits, addMatrixBitsProg_correct]
  rfl
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost BinaryPolynomial BinaryLinear
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
/-- Every generated quotient element is idempotent. -/
theorem fixedGenerator_idempotent (j : Fin f.natDegree) :
    fixedGenerator f hf j * fixedGenerator f hf j = fixedGenerator f hf j := by
  apply (fixedMatrix_ker f hf _).mp
  rw [fixedGenerator, LinearEquiv.apply_symm_apply]
  exact kernelMap_mem_ker _ _
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost BinaryPolynomial BinaryLinear
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
/-- The program prints exactly the canonical coordinates of these generators. -/
theorem fixedGeneratorsProg_correct (p : BitStr)
    (hp : p.length = f.natDegree) (hpoly : f = polyOfBits (p ++ [true])) :
    fixedGeneratorsProg p = List.ofFn (fun j => toBits f hf (fixedGenerator f hf j)) := by
  simp only [fixedGeneratorsProg, Cost.PolyTimeFun.comp_apply,
    Cost.PolyTimeFun.pair_apply, Cost.PolyTimeFun.length_apply]
  rw [hp, fixedMatrixProg_correct f hf p hp hpoly, kernelGeneratorsProg_encoding]
  apply congrArg List.ofFn
  funext j
  rw [toBits_eq_vectorBits, fixedGenerator, LinearEquiv.apply_symm_apply]
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun Polynomial BinaryPolynomial
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
include hf in
/-- The quotient dimension is the degree of the monic modulus. -/
theorem finrank_eq : Module.finrank (ZMod 2) (AdjoinRoot f) = f.natDegree := by
  rw [(coordinateEquiv f hf).finrank_eq]
  simp
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun Polynomial BinaryPolynomial
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
/-- The list cap is inert on a genuine family of orthogonal quotient idempotents. -/
theorem splitBitsCapped_encoding (p : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true]))
    (l : List (AdjoinRoot f)) (hl : ComponentFamily l)
    (b : AdjoinRoot f) (hb : b * b = b) :
    splitBitsCapped p (l.map (toBits f hf)) (toBits f hf b) =
      (splitComponents l b).map (toBits f hf) := by
  have he : (l.map (toBits f hf)).flatMap (fun e => splitBits p e (toBits f hf b)) =
      (splitComponents l b).map (toBits f hf) := by
    simp only [List.flatMap_map, splitBits_encoding f hf p hp hpoly,
      splitComponents, List.map_flatMap]
  unfold splitBitsCapped
  rw [he, List.take_of_length_le]
  let : Module.Finite (ZMod 2) (AdjoinRoot f) :=
    Module.Finite.equiv (coordinateEquiv f hf).symm
  simpa only [List.length_map, finrank_eq f hf, hp] using (hl.split hb).length_le_finrank
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun Polynomial BinaryPolynomial
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
/-- The complete encoded refinement agrees with abstract component refinement. -/
theorem fold_componentStep_encoding (p : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true]))
    (bs l : List (AdjoinRoot f)) (hl : ComponentFamily l)
    (hb : ∀ b ∈ bs, b * b = b) :
    (bs.map (toBits f hf)).foldl componentStep (p, l.map (toBits f hf)) =
      (p, (splitAllComponents l bs).map (toBits f hf)) := by
  induction bs generalizing l with
  | nil => rfl
  | cons b bs ih =>
    have hbb := hb b (by simp)
    rw [List.map_cons, List.foldl_cons]
    change (bs.map _).foldl componentStep (p, splitBitsCapped _ _ _) = _
    rw [splitBitsCapped_encoding f hf p hp hpoly l hl b hbb, ih _ (hl.split hbb)
      (fun x hx => hb x (by simp [hx]))]
    rfl
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun Polynomial BinaryPolynomial
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
/-- Every generator in the computed fixed-space family is idempotent. -/
theorem fixedFamily_idempotent : ∀ b ∈ fixedFamily f hf, b * b = b := by
  intro b hb
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
  exact fixedGenerator_idempotent f hf j
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun Polynomial BinaryPolynomial
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
/-- Fixed-width one is the canonical encoding of the quotient unit. -/
theorem oneBits_toBits (p : BitStr) (hp : p.length = f.natDegree) (hp0 : p ≠ []) :
    oneBits p = toBits f hf 1 := by
  apply (evalBits_eq_iff f hf _ _ ((length_oneBits p).trans hp) (length_toBits f hf 1)).mp
  rw [evalBits_oneBits _ p hp0, evalBits_toBits]
end
end MIPRE.LowDegree.BinaryQuotient

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryQuotient
open Cost Cost.PolyTimeFun Polynomial BinaryPolynomial
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
theorem _root_.solution (p : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true])) (hp0 : p ≠ []) :
    quotientComponentsProg p = (components f hf).map (toBits f hf) := by
  have hdegree : f.degree ≠ 0 := by
    rw [degree_eq_natDegree hf.ne_zero]
    have hlen : 0 < p.length := List.length_pos_iff.mpr hp0
    exact_mod_cast (show f.natDegree ≠ 0 by omega)
  let : Nontrivial (AdjoinRoot f) := AdjoinRoot.nontrivial f hdegree
  have hg : fixedGeneratorsProg p = (fixedFamily f hf).map (toBits f hf) := by
    rw [fixedGeneratorsProg_correct f hf p hp hpoly]
    simp only [fixedFamily, List.map_ofFn]
    rfl
  have hu : ComponentFamily ([1] : List (AdjoinRoot f)) := by constructor <;> simp
  change ((fixedGeneratorsProg p).foldl componentStep (p, [oneBits p])).2 = _
  rw [hg, oneBits_toBits f hf p hp hp0]
  change (((fixedFamily f hf).map (toBits f hf)).foldl componentStep
    (p, ([1] : List (AdjoinRoot f)).map (toBits f hf))).2 = _
  rw [fold_componentStep_encoding f hf p hp hpoly _ _ hu (fixedFamily_idempotent f hf)]
  rfl
end MIPRE.LowDegree.BinaryQuotient
