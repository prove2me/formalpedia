-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryQuotient.coeffPolynomial_linearMulCarry
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:44:49.763338+00:00
-- url     : https://prove2.me/submissions/3dfeed79-bf51-4b21-96ff-3a355f23fa19

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryQuotientOrbit.lean (solution of MIPRE.LowDegree.BinaryQuotient.coeffPolynomial_linearMulCarry);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_mulReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_xor
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_mulReduce

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryQuotient
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R]
theorem _root_.solution [CharP R 2] (z : R)
    (p a carry : BitStr) (cs : List BitStr)
    (hz : z ^ p.length = evalBits z p)
    (ha : a.length = p.length) (hc : carry.length = p.length)
    (hs : ∀ c ∈ cs, c.length = p.length) :
    coeffPolynomial z (linearMulCarry p a carry cs) =
      C (evalBits z carry) + (X + C (evalBits z a)) * coeffPolynomial z cs := by
  induction cs generalizing carry with
  | nil =>
    simp only [linearMulCarry, List.map_nil, List.nil_append, List.zipWith_cons_cons,
      List.zipWith_nil_left, coeffPolynomial_cons, coeffPolynomial_nil, mul_zero, add_zero]
    rw [evalBits_xor z _ _ (by simp [hc]), evalBits_zeroBits, add_zero]
  | cons c cs ih =>
    have hhead := hs c (by simp)
    have htail : ∀ d ∈ cs, d.length = p.length := fun d hd => hs d (by simp [hd])
    change C (evalBits z (xorBits carry (mulReduce p a c))) +
      X * coeffPolynomial z (linearMulCarry p a c cs) = _
    rw [evalBits_xor z _ _ (hc.trans (length_mulReduce p a c ha).symm),
      evalBits_mulReduce z p a c ha hz, ih c hhead htail, coeffPolynomial_cons]
    simp only [map_add, map_mul]
    ring
end MIPRE.LowDegree.BinaryQuotient
