-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryPolynomial.evalBits_mulReduce
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:49:05.566153+00:00
-- url     : https://prove2.me/submissions/2c41cbdb-f9e4-4af9-adba-e93a2485676e

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryPolynomial.lean (solution of MIPRE.LowDegree.BinaryPolynomial.evalBits_mulReduce);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_shiftReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_xor
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_mulReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_shiftReduce

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryPolynomial
open Cost
variable {R : Type*} [CommRing R]
theorem _root_.solution [CharP R 2] (z : R) (p a b : BitStr)
    (hlen : a.length = p.length) (hroot : z ^ p.length = evalBits z p) :
    evalBits z (mulReduce p a b) = evalBits z a * evalBits z b := by
  induction b with
  | nil => simp [mulReduce]
  | cons bit b ih =>
    change evalBits z (if bit then xorBits (shiftReduce p (mulReduce p a b)) a
      else shiftReduce p (mulReduce p a b)) = _
    have hl := length_mulReduce p a b hlen
    cases bit
    · simp only [Bool.false_eq_true, if_false, evalBits_cons, ofBool, zero_add]
      rw [evalBits_shiftReduce z p _ hl hroot, ih]
      ring
    · simp only [if_true, evalBits_cons, ofBool]
      rw [evalBits_xor z _ _ (by rw [length_shiftReduce p _ hl, hlen]),
        evalBits_shiftReduce z p _ hl hroot, ih]
      ring
end MIPRE.LowDegree.BinaryPolynomial
