-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryQuotient.evalBits_fold_traceStep
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:45:36.809045+00:00
-- url     : https://prove2.me/submissions/9c4f6074-4f1f-4091-8d60-8e3ba675fe0d

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryTraceBits.lean (solution of MIPRE.LowDegree.BinaryQuotient.evalBits_fold_traceStep);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Algebra
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
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientOrbit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryTraceBits
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_mulReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_xor
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_mulReduce

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R]
/-- Repeated squaring preserves the fixed-width representation. -/
theorem iterate_squareStep_width (n : ℕ) (p a : BitStr) (ha : a.length = p.length) :
    (squareStep^[n] (p, a)).2.length = p.length := by
  induction n generalizing a with
  | zero => exact ha
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih _ (length_mulReduce p a a ha)
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R]
/-- Repeated squaring computes the corresponding Frobenius power. -/
theorem evalBits_iterate_squareStep [CharP R 2] (z : R) (n : ℕ) (p a : BitStr)
    (hz : z ^ p.length = evalBits z p) (ha : a.length = p.length) :
    evalBits z (squareStep^[n] (p, a)).2 = evalBits z a ^ (2 ^ n) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change evalBits z (squareStep^[n] (p, mulReduce p a a)).2 = _
    rw [ih _ (length_mulReduce p a a ha), evalBits_mulReduce z p a a ha hz]
    rw [← pow_two, ← pow_mul, pow_succ, Nat.mul_comm (2 ^ n) 2]
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
/-- The modulus width is preserved on valid quotient elements. -/
theorem frobeniusBits_width (u : Unary) (p a : BitStr) (ha : a.length = p.length) :
    (frobeniusBits u p a).length = p.length := iterate_squareStep_width u.length p a ha
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
/-- The supplied stride is the exponent of the Frobenius iterate. -/
theorem evalBits_frobeniusBits {R : Type*} [CommRing R] [CharP R 2]
    (z : R) (u : Unary) (p a : BitStr) (hz : z ^ p.length = evalBits z p)
    (ha : a.length = p.length) :
    evalBits z (frobeniusBits u p a) = evalBits z a ^ (2 ^ u.length) :=
  evalBits_iterate_squareStep z u.length p a hz ha
end
end MIPRE.LowDegree.BinaryQuotient

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryQuotient
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
theorem _root_.solution {R : Type*} [CommRing R] [CharP R 2]
    (z : R) (u r : Unary) (p c a : BitStr) (hz : z ^ p.length = evalBits z p)
    (hc : c.length = p.length) (ha : a.length = p.length) :
    evalBits z (u.foldl traceStep (r, p, c, a)).2.2.1 =
      evalBits z c + ∑ i ∈ Finset.range u.length, evalBits z a ^ (2 ^ (r.length * i)) := by
  induction u generalizing c a with
  | nil => simp
  | cons b u ih =>
    change evalBits z (u.foldl traceStep
      (r, p, xorBits c a, frobeniusBits r p a)).2.2.1 = _
    rw [ih _ _ (by simp [length_xorBits, hc, ha]) (frobeniusBits_width r p a ha),
      evalBits_xor z c a (hc.trans ha.symm), evalBits_frobeniusBits z r p a hz ha]
    have hs : ∑ i ∈ Finset.range u.length,
        (evalBits z a ^ (2 ^ r.length)) ^ (2 ^ (r.length * i)) =
        ∑ i ∈ Finset.range u.length, evalBits z a ^ (2 ^ (r.length * (i + 1))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← pow_mul, ← pow_add]
      congr 2
      simp only [Nat.mul_add, Nat.mul_one, Nat.add_comm]
    rw [hs, List.length_cons, Finset.sum_range_succ']
    simp only [Nat.mul_zero, pow_zero, pow_one]
    ring
end MIPRE.LowDegree.BinaryQuotient
