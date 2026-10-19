-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryPolynomial.cyclotomicSeedBits_canonical
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:18:15.005+00:00
-- url     : https://prove2.me/submissions/032e1211-7c69-46a2-94b7-f29de8c3d56e

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryNonresidueCorrectness.lean (solution of MIPRE.LowDegree.BinaryPolynomial.cyclotomicSeedBits_canonical);
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
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCyclotomicSeed
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySubstitution
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueLoop
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueCorrectness
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_cyclotomicSeedBits_correct
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_gcdStep_correct

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
namespace MIPRE.LowDegree.BinaryPolynomial
open Cost Polynomial
theorem _root_.solution (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    (cyclotomicSeedBits (unary q)).getLastD false = true := by
  have hi := (cyclotomicSeedBits_correct q hq hq2).2.1
  cases hl : BinaryQuotient.factorBitsProg (cyclotomicLowerBits (unary q)) with
  | nil =>
    have he : cyclotomicSeedBits (unary q) = [] := by unfold cyclotomicSeedBits; rw [hl]; rfl
    exact (hi.ne_zero (by rw [he]; simp [polyOfBits])).elim
  | cons a l =>
    have hcan := BinaryQuotient.factorBitsProg_canonical (cyclotomicLowerBits (unary q))
      a (by rw [hl]; exact List.mem_cons_self)
    have he : cyclotomicSeedBits (unary q) = a := by unfold cyclotomicSeedBits; rw [hl]; rfl
    rw [he] at hi ⊢
    rcases hcan with hn | hn
    · exact (hi.ne_zero (by rw [hn]; simp [polyOfBits])).elim
    · exact hn
end MIPRE.LowDegree.BinaryPolynomial
