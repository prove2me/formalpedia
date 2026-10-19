-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryQuotient.factor_dropLast_factors
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:14:26.672511+00:00
-- url     : https://prove2.me/submissions/a99505a9-afb5-46be-827b-04d2e3f04492

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryFactorizationCanonical.lean (solution of MIPRE.LowDegree.BinaryQuotient.factor_dropLast_factors);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_gcdStep_correct
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_monic_polyOfBits_append_true
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_natDegree_polyOfBits_append_true
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_factorBitsProg_factors

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
/-- For a nonzero canonical representation, width is degree plus one. -/
theorem natDegree_add_one_of_getLast (a : BitStr) (h : a.getLastD false = true) :
    (polyOfBits a).natDegree + 1 = a.length := by
  have hn : a ≠ [] := by intro he; simp [he] at h
  have hl : 0 < a.length := List.length_pos_iff.mpr hn
  have hd := natDegree_polyOfBits_append_true a.dropLast
  rw [dropLast_append_true a h, List.length_dropLast] at hd
  omega
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
/-- Both Euclidean state entries retain a canonical binary representation. -/
theorem fold_gcdStep_canonical (l : BitStr) (s : GCDState)
    (ha : s.1 = [] ∨ s.1.getLastD false = true)
    (hb : s.2 = [] ∨ s.2.getLastD false = true) :
    ((l.foldl gcdStep s).1 = [] ∨ (l.foldl gcdStep s).1.getLastD false = true) ∧
    ((l.foldl gcdStep s).2 = [] ∨ (l.foldl gcdStep s).2.getLastD false = true) := by
  induction l generalizing s with
  | nil => exact ⟨ha, hb⟩
  | cons b l ih =>
    apply ih (gcdStep s b)
    · unfold gcdStep
      split
      · exact ha
      · exact hb
    · exact (gcdStep_correct s b hb).2
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
/-- The gcd output has no trailing zero coefficient. -/
theorem gcdBits_canonical (a b : BitStr) :
    gcdBits a b = [] ∨ (gcdBits a b).getLastD false = true :=
  (fold_gcdStep_canonical b (normalizeBits a, normalizeBits b)
    (normalizeBits_getLast a) (normalizeBits_getLast b)).1
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryQuotient
section
open Cost Polynomial BinaryPolynomial
/-- Every printed factor uses a canonical coefficient representation. -/
theorem factorBitsProg_canonical (p : BitStr) :
    ∀ a ∈ factorBitsProg p, a = [] ∨ a.getLastD false = true := by
  intro a ha
  change a ∈ (quotientComponentsProg p).map
    (fun e => gcdBits (p ++ [true]) (xorBits e (oneBits p))) at ha
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp ha
  exact gcdBits_canonical _ _
end
end MIPRE.LowDegree.BinaryQuotient

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryQuotient
open Cost Polynomial BinaryPolynomial
theorem _root_.solution (a : BitStr) (ha : a.getLastD false = true)
    (hp : 0 < (polyOfBits a).natDegree) (hs : Squarefree (polyOfBits a)) :
    ∀ b ∈ factorBitsProg a.dropLast,
      b.getLastD false = true ∧ (polyOfBits b).Monic ∧ Irreducible (polyOfBits b) := by
  have hd := natDegree_add_one_of_getLast a ha
  have hf := factorBitsProg_factors (polyOfBits a) (monic_polyOfBits_of_getLast a ha)
    a.dropLast (by simp only [List.length_dropLast]; omega)
    (by rw [dropLast_append_true a ha])
    (by intro he; have hl := congrArg List.length he
        simp only [List.length_dropLast, List.length_nil] at hl; omega) hs
  intro b hb
  have hi := hf b hb
  refine ⟨?_, hi⟩
  rcases factorBitsProg_canonical a.dropLast b hb with h | h
  · subst b
    exact (hi.2.ne_zero (by simp [polyOfBits])).elim
  · exact h
end MIPRE.LowDegree.BinaryQuotient
