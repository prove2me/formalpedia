-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryQuotient.factorBitsProg_factors
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:12:24.746004+00:00
-- url     : https://prove2.me/submissions/82724342-1484-4ddd-8998-49538c4ad7f6

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryFactorization.lean (solution of MIPRE.LowDegree.BinaryQuotient.factorBitsProg_factors);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Squarefree.Basic
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
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGCD
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFactorization
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_IsPivotBasis_append_reduced
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_IsPivotBasis_eq_zero_of_pivots_zero
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_binary_eq_zero_or_one
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_getD_vectorBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_typedBasis_span
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_divModBits_width
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_oneBits
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_xor
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_gcdStep_correct
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_monic_polyOfBits_append_true
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_componentFactor_prime
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_fixedMatrix_ker
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_quotientComponentsProg_correct
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_square_injective
import Theorems.Thm_MIPRE_LowDegree_ComponentFamily_split
import Theorems.Thm_MIPRE_LowDegree_decidesComponent_of_mem_span

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost
/-- The polynomial used by Shoup's contract reads the same coefficient bits. -/
theorem coeff_polyOfBits (l : BitStr) (i : ℕ) :
    (polyOfBits l).coeff i = ofBool (l.getD i false) := by
  simp only [polyOfBits, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases hi : i < l.length
  · simp [hi, ofBool]
  · simp [hi, ofBool, List.getD_eq_getElem?_getD]
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost
theorem polyOfBits_cons (b : Bool) (l : BitStr) :
    polyOfBits (b :: l) = Polynomial.C (ofBool b) + Polynomial.X * polyOfBits l := by
  ext i
  cases i <;> simp [coeff_polyOfBits, Polynomial.coeff_X_mul]
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
/-- Normalizing cannot increase the coefficient width. -/
theorem length_normalizeStep_le (a : BitStr) (b : Bool) :
    (normalizeStep a b).length ≤ a.length + 1 := by
  cases b <;> simp [normalizeStep]
  split <;> simp
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
/-- The normalized representation is no longer than its input. -/
theorem length_normalizeBits_le (a : BitStr) : (normalizeBits a).length ≤ a.length := by
  induction a with
  | nil => simp
  | cons b a ih =>
    rw [normalizeBits_cons]
    have hs := length_normalizeStep_le (normalizeBits a) b
    simp only [List.length_cons]
    omega
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
/-- Suppression of high zero coefficients preserves evaluation in every ring. -/
theorem evalBits_normalizeStep {R : Type*} [CommRing R] (z : R) (a : BitStr) (b : Bool) :
    evalBits z (normalizeStep a b) = ofBool b + z * evalBits z a := by
  cases b <;> cases a <;> simp [normalizeStep, ofBool]
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
/-- Normalization preserves Horner evaluation. -/
theorem evalBits_normalizeBits {R : Type*} [CommRing R] (z : R) (a : BitStr) :
    evalBits z (normalizeBits a) = evalBits z a := by
  induction a with
  | nil => rfl
  | cons b a ih => rw [normalizeBits_cons, evalBits_normalizeStep, ih, evalBits_cons]
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
/-- The polynomial interpretation is Horner evaluation at the indeterminate. -/
theorem polyOfBits_eq_evalBits (a : BitStr) :
    polyOfBits a = evalBits (X : Polynomial (ZMod 2)) a := by
  induction a with
  | nil => simp [polyOfBits]
  | cons b a ih =>
    rw [polyOfBits_cons, evalBits_cons, ih]
    cases b <;> simp [ofBool]
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
/-- Normalization preserves the polynomial itself. -/
theorem polyOfBits_normalizeBits (a : BitStr) :
    polyOfBits (normalizeBits a) = polyOfBits a := by
  simpa only [polyOfBits_eq_evalBits] using evalBits_normalizeBits (X : Polynomial (ZMod 2)) a
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
/-- A nonempty normalized list has a leading coefficient equal to one. -/
theorem normalizeBits_getLast (a : BitStr) :
    normalizeBits a = [] ∨ (normalizeBits a).getLastD false = true := by
  induction a with
  | nil => exact Or.inl rfl
  | cons b a ih =>
    rcases ih with h | h
    · cases b <;> simp [normalizeBits_cons, normalizeStep, h]
    · have hn : normalizeBits a ≠ [] := by intro he; simp [he] at h
      cases ha : normalizeBits a with
      | nil => exact (hn ha).elim
      | cons c a =>
        cases b <;> simpa [normalizeBits_cons, normalizeStep, ha, List.getLastD_cons] using h
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Polynomial
/-- A list with a true leading bit decomposes into its lower coefficients and that bit. -/
theorem dropLast_append_true (a : BitStr) (h : a.getLastD false = true) :
    a.dropLast ++ [true] = a := by
  have hn : a ≠ [] := by intro he; simp [he] at h
  have hh : a.getLast hn = true := by
    cases a with
    | nil => exact (hn rfl).elim
    | cons b a => simpa only [List.getLast_eq_getLastD, List.getLastD_cons] using h
  simpa only [hh] using List.dropLast_append_getLast hn
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Polynomial
/-- A coefficient list with leading bit one represents a monic polynomial. -/
theorem monic_polyOfBits_of_getLast (a : BitStr) (h : a.getLastD false = true) :
    (polyOfBits a).Monic := by
  rw [← dropLast_append_true a h]
  exact monic_polyOfBits_append_true _
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Polynomial
/-- Normalizing produces the empty list exactly when the polynomial is zero. -/
theorem normalizeBits_eq_nil_iff (a : BitStr) :
    normalizeBits a = [] ↔ polyOfBits a = 0 := by
  constructor
  · intro h
    rw [← polyOfBits_normalizeBits a, h]
    simp [polyOfBits]
  · intro h
    rcases normalizeBits_getLast a with hn | hn
    · exact hn
    · have hm := monic_polyOfBits_of_getLast _ hn
      rw [polyOfBits_normalizeBits, h] at hm
      exact (hm.ne_zero rfl).elim
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Polynomial
/-- Over the binary field, every nonzero polynomial represented by bits is monic. -/
theorem monic_polyOfBits (a : BitStr) (ha : polyOfBits a ≠ 0) :
    (polyOfBits a).Monic := by
  rcases normalizeBits_getLast a with hn | hn
  · exact (ha ((normalizeBits_eq_nil_iff a).mp hn)).elim
  · simpa only [polyOfBits_normalizeBits] using monic_polyOfBits_of_getLast _ hn
end
end MIPRE.LowDegree.BinaryPolynomial

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
/-- All idempotents lie in the binary span of the computed generator family. -/
theorem fixedGenerator_spans (x : AdjoinRoot f) (hx : x * x = x) :
    x ∈ Submodule.span (ZMod 2) (Set.range (fixedGenerator f hf)) := by
  have hc := (fixedMatrix_ker f hf x).mpr hx
  rw [← kernel_generators_span] at hc
  have hm : x ∈ Submodule.map (coordinateEquiv f hf).symm.toLinearMap
      (Submodule.span (ZMod 2) (Set.range (fun j : Fin f.natDegree =>
        kernelMap (fixedMatrix f hf) (Pi.single j 1)))) :=
    Submodule.mem_map.mpr
      ⟨coordinateEquiv f hf x, hc, (coordinateEquiv f hf).symm_apply_apply x⟩
  rw [Submodule.map_span, ← Set.range_comp] at hm
  exact hm
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
/-- All quotient idempotents lie in the span of the computed family. -/
theorem fixedFamily_spans (z : AdjoinRoot f) (hz : z * z = z) :
    z ∈ Submodule.span (ZMod 2) {b | b ∈ fixedFamily f hf} := by
  have hs : {b | b ∈ fixedFamily f hf} = Set.range (fixedGenerator f hf) := by
    ext b
    simp [fixedFamily]
  rw [hs]
  exact fixedGenerator_spans f hf z hz
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun Polynomial BinaryPolynomial
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
/-- Separation of the complete fixed space makes every returned component primitive. -/
theorem components_primitive [Nontrivial (AdjoinRoot f)] :
    ∀ e ∈ components f hf, PrimitiveBinaryComponent e := by
  have hu : ComponentFamily ([1] : List (AdjoinRoot f)) := by constructor <;> simp
  exact splitAllComponents_primitive hu (fixedFamily_idempotent f hf) (fixedFamily_spans f hf)
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Polynomial
/-- Irreducibility follows from the primitive-component primality criterion. -/
theorem componentFactor_irreducible (f E : Polynomial (ZMod 2)) (hf : f ≠ 0)
    [Finite (AdjoinRoot f)]
    (hsq : Function.Bijective (fun x : AdjoinRoot f => x * x))
    (he : PrimitiveBinaryComponent (AdjoinRoot.mk f E)) :
    Irreducible (componentFactor f E) :=
  (componentFactor_prime f E hf hsq he).irreducible
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Polynomial
/-- Every nonzero quotient modulus has a monic supported gcd factor. -/
theorem componentFactor_monic (f E : Polynomial (ZMod 2)) (hf : f ≠ 0) :
    (componentFactor f E).Monic := by
  have hne : componentFactor f E ≠ 0 :=
    ne_zero_of_dvd_ne_zero hf (gcd_dvd_left f (E - 1))
  simpa only [componentFactor, normalize_gcd] using (Polynomial.monic_normalize hne)
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
section
variable (f : Polynomial (ZMod 2))
/-- A monic quotient is finite in its specified power-basis coordinates, so
injective squaring is bijective. No field or irreducibility assumption is used. -/
theorem square_bijective (hf : f.Monic) (hs : Squarefree f) :
    Function.Bijective (fun x : AdjoinRoot f => x * x) := by
  let : Fintype (AdjoinRoot f) :=
    Fintype.ofEquiv (Fin f.natDegree → ZMod 2) (coordinateEquiv f hf).symm.toEquiv
  exact ⟨square_injective f hs, Finite.surjective_of_injective (square_injective f hs)⟩
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
/-- The divisor width decreases on every nonterminal step, even on malformed states. -/
theorem gcdStep_second_length (s : GCDState) (b : Bool) :
    (gcdStep s b).2.length ≤ s.2.length - 1 := by
  by_cases hs : s.2 = []
  · simp [gcdStep, hs]
  · simpa only [gcdStep, List.isEmpty_eq_false_iff.mpr hs, Bool.false_eq_true, if_false,
      List.length_dropLast] using (divModBits_width s.2.dropLast s.1).2
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
/-- Each fuel bit removes one possible remaining divisor coefficient. -/
theorem fold_gcdStep_second_length (l : BitStr) (s : GCDState) :
    (l.foldl gcdStep s).2.length ≤ s.2.length - l.length := by
  induction l generalizing s with
  | nil => simp
  | cons b l ih =>
    have hi := ih (gcdStep s b)
    have hs := gcdStep_second_length s b
    simp only [List.foldl_cons, List.length_cons]
    omega
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
/-- Binary polynomials are already normalized as elements of the gcd monoid. -/
theorem normalize_polyOfBits (a : BitStr) : normalize (polyOfBits a) = polyOfBits a := by
  by_cases h : polyOfBits a = 0
  · simp [h]
  · exact (monic_polyOfBits a h).normalize_eq_self
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
/-- The complete Euclidean loop preserves the polynomial gcd. -/
theorem fold_gcdStep_correct (l : BitStr) (s : GCDState)
    (hs : s.2 = [] ∨ s.2.getLastD false = true) :
    gcd (polyOfBits (l.foldl gcdStep s).1) (polyOfBits (l.foldl gcdStep s).2) =
      gcd (polyOfBits s.1) (polyOfBits s.2) := by
  induction l generalizing s with
  | nil => rfl
  | cons b l ih =>
    have h := gcdStep_correct s b hs
    exact (ih (gcdStep s b) h.2).trans h.1
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
/-- The executable algorithm computes Mathlib's normalized polynomial gcd. -/
theorem polyOfBits_gcdBits (a b : BitStr) :
    polyOfBits (gcdBits a b) = gcd (polyOfBits a) (polyOfBits b) := by
  have hlen := fold_gcdStep_second_length b (normalizeBits a, normalizeBits b)
  have hb := length_normalizeBits_le b
  have hz : (b.foldl gcdStep (normalizeBits a, normalizeBits b)).2 = [] := by
    apply List.length_eq_zero_iff.mp
    simp only at hlen
    omega
  have h := fold_gcdStep_correct b (normalizeBits a, normalizeBits b) (normalizeBits_getLast b)
  rw [hz, show polyOfBits [] = 0 by simp [polyOfBits], gcd_zero_right,
    normalize_polyOfBits, polyOfBits_normalizeBits, polyOfBits_normalizeBits] at h
  exact h
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun Polynomial BinaryPolynomial
/-- XOR is binary polynomial addition on equal-width lists. -/
theorem polyOfBits_xorBits (a b : BitStr) (h : a.length = b.length) :
    polyOfBits (xorBits a b) = polyOfBits a + polyOfBits b := by
  simpa only [polyOfBits_eq_evalBits] using evalBits_xor (X : Polynomial (ZMod 2)) a b h
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun Polynomial BinaryPolynomial
/-- Fixed-width one represents the constant polynomial one at every positive width. -/
theorem polyOfBits_oneBits (p : BitStr) (hp : p ≠ []) : polyOfBits (oneBits p) = 1 := by
  simpa only [polyOfBits_eq_evalBits] using evalBits_oneBits (X : Polynomial (ZMod 2)) p hp
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun Polynomial BinaryPolynomial
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
/-- The extracted coefficient lists represent precisely the primitive-component factors. -/
theorem factorBitsProg_polynomials (p : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true])) (hp0 : p ≠ []) :
    (factorBitsProg p).map polyOfBits =
      (components f hf).map (fun e => componentFactor f (polyOfBits (toBits f hf e))) := by
  change ((quotientComponentsProg p).map
    (fun e => gcdBits (p ++ [true]) (xorBits e (oneBits p)))).map polyOfBits = _
  rw [quotientComponentsProg_correct f hf p hp hpoly hp0, List.map_map, List.map_map]
  apply List.map_congr_left
  intro e _
  change polyOfBits (gcdBits (p ++ [true]) (xorBits (toBits f hf e) (oneBits p))) = _
  rw [polyOfBits_gcdBits, polyOfBits_xorBits _ _ (by simp [hp]), polyOfBits_oneBits p hp0]
  rw [← hpoly, componentFactor, CharTwo.sub_eq_add]
end
end MIPRE.LowDegree.BinaryQuotient

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryQuotient
open Cost Cost.PolyTimeFun Polynomial BinaryPolynomial
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
include hf in
theorem _root_.solution (p : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true])) (hp0 : p ≠ []) (hs : Squarefree f) :
    ∀ a ∈ factorBitsProg p, (polyOfBits a).Monic ∧ Irreducible (polyOfBits a) := by
  have hdegree : f.degree ≠ 0 := by
    rw [degree_eq_natDegree hf.ne_zero]
    have hlen : 0 < p.length := List.length_pos_iff.mpr hp0
    exact_mod_cast (show f.natDegree ≠ 0 by omega)
  let : Nontrivial (AdjoinRoot f) := AdjoinRoot.nontrivial f hdegree
  let : Fintype (AdjoinRoot f) :=
    Fintype.ofEquiv (Fin f.natDegree → ZMod 2) (coordinateEquiv f hf).symm.toEquiv
  intro a ha
  have hm : polyOfBits a ∈ (factorBitsProg p).map polyOfBits := List.mem_map.mpr ⟨a, ha, rfl⟩
  rw [factorBitsProg_polynomials f hf p hp hpoly hp0] at hm
  obtain ⟨e, he, hE⟩ := List.mem_map.mp hm
  rw [← hE]
  refine ⟨componentFactor_monic f _ hf.ne_zero, ?_⟩
  apply componentFactor_irreducible f _ hf.ne_zero (square_bijective f hf hs)
  rw [mk_polyOfBits_toBits]
  exact components_primitive f hf e he
end MIPRE.LowDegree.BinaryQuotient
