-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryPolynomial.evalBits_shiftReduce
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:47:48.054174+00:00
-- url     : https://prove2.me/submissions/b08f6b87-cdc1-496c-95fc-4e0599221b86

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryPolynomial.lean (solution of MIPRE.LowDegree.BinaryPolynomial.evalBits_shiftReduce);
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
open Cost
variable {R : Type*} [CommRing R]
theorem _root_.solution [CharP R 2] (z : R) (p a : BitStr)
    (hlen : a.length = p.length) (hroot : z ^ p.length = evalBits z p) :
    evalBits z (shiftReduce p a) = z * evalBits z a := by
  have h := evalBits_shiftLow z a
  unfold shiftReduce
  split <;> rename_i hb
  · rw [evalBits_xor z _ _ (by simp [hlen])]
    rw [hb] at h
    simpa [ofBool, hlen, hroot] using h
  · have hb' : a.getLastD false = false := Bool.eq_false_iff.mpr hb
    rw [hb'] at h
    simpa [ofBool] using h
end MIPRE.LowDegree.BinaryPolynomial
