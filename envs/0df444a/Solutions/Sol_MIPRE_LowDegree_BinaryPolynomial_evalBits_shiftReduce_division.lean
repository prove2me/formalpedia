-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryPolynomial.evalBits_shiftReduce_division
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:47:06.838899+00:00
-- url     : https://prove2.me/submissions/9bcada83-4e2f-4ee0-a253-3365469a28f8

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryDivision.lean (solution of MIPRE.LowDegree.BinaryPolynomial.evalBits_shiftReduce_division);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDivision
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_xor

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost
variable {R : Type*} [CommRing R]
theorem evalBits_append (z : R) (a b : BitStr) :
    evalBits z (a ++ b) = evalBits z a + z ^ a.length * evalBits z b := by
  induction a with
  | nil => simp
  | cons x a ih => simp only [List.cons_append, evalBits_cons, ih, List.length_cons, pow_succ]; ring
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost
variable {R : Type*} [CommRing R]
theorem evalBits_shiftLow (z : R) (a : BitStr) :
    evalBits z (shiftLow a) + z ^ a.length * ofBool (a.getLastD false) =
      z * evalBits z a := by
  have h : shiftLow a ++ [a.getLastD false] = false :: a := by
    simpa only [shiftLow, List.getLast_eq_getLastD] using
      List.dropLast_append_getLast (List.cons_ne_nil false a)
  have he := congrArg (evalBits z) h
  simpa [evalBits_append, ofBool] using he
end
end MIPRE.LowDegree.BinaryPolynomial

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryPolynomial
open Cost Cost.PolyTimeFun Polynomial
variable {R : Type*} [CommRing R] [CharP R 2]
theorem _root_.solution (z : R) (p a : BitStr)
    (hlen : a.length = p.length) :
    evalBits z (shiftReduce p a) +
      (evalBits z p + z ^ p.length) * ofBool (a.getLastD false) = z * evalBits z a := by
  have h := evalBits_shiftLow z a
  unfold shiftReduce
  cases hb : a.getLastD false
  · rw [hb] at h
    simpa only [Bool.false_eq_true, if_false, ofBool, mul_zero, add_zero] using h
  · rw [hb] at h
    simp only [if_true, ofBool, mul_one]
    rw [evalBits_xor z _ _ ((length_shiftLow a).trans hlen)]
    calc
      evalBits z (shiftLow a) + evalBits z p + (evalBits z p + z ^ p.length) =
          evalBits z (shiftLow a) + z ^ p.length + (evalBits z p + evalBits z p) := by ring
      _ = z * evalBits z a := by
        rw [CharTwo.add_self_eq_zero, add_zero]
        simpa only [hlen, ofBool, if_true, mul_one] using h
end MIPRE.LowDegree.BinaryPolynomial
