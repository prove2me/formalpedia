-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryPolynomial.evalBits_divisionStep
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:47:53.952552+00:00
-- url     : https://prove2.me/submissions/bfd9a8b2-409f-451a-b73a-58301e1a093d

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryDivision.lean (solution of MIPRE.LowDegree.BinaryPolynomial.evalBits_divisionStep);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_oneBits
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_shiftReduce_division
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_xor
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_shiftReduce

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryPolynomial
open Cost Cost.PolyTimeFun Polynomial
variable {R : Type*} [CommRing R] [CharP R 2]
theorem _root_.solution (z : R) (p q r : BitStr) (b : Bool) (hp : p ≠ [])
    (hr : r.length = p.length) :
    (evalBits z p + z ^ p.length) * evalBits z (divisionStep (p, q, r) b).2.1 +
      evalBits z (divisionStep (p, q, r) b).2.2 =
    ofBool b + z * ((evalBits z p + z ^ p.length) * evalBits z q + evalBits z r) := by
  have hs := evalBits_shiftReduce_division z p r hr
  have hl : (shiftReduce p r).length = (oneBits p).length := by
    rw [length_shiftReduce p r hr, length_oneBits]
  have h0 : (ofBool false : R) = 0 := rfl
  have h1 : (ofBool true : R) = 1 := rfl
  cases b <;> simp only [divisionStep, Bool.false_eq_true, if_false, if_true, evalBits_cons,
    h0, h1, zero_add, evalBits_xor z _ _ hl, evalBits_oneBits z p hp]
  · calc
      _ = z * ((evalBits z p + z ^ p.length) * evalBits z q) +
          (evalBits z (shiftReduce p r) +
            (evalBits z p + z ^ p.length) * ofBool (r.getLastD false)) := by ring
      _ = _ := by rw [hs]; ring
  · calc
      _ = 1 + z * ((evalBits z p + z ^ p.length) * evalBits z q) +
          (evalBits z (shiftReduce p r) +
            (evalBits z p + z ^ p.length) * ofBool (r.getLastD false)) := by ring
      _ = _ := by rw [hs]; ring
end MIPRE.LowDegree.BinaryPolynomial
