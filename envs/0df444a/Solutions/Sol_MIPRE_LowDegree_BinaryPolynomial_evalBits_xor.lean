-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryPolynomial.evalBits_xor
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:45:45.266383+00:00
-- url     : https://prove2.me/submissions/6bc56625-d4b7-423d-9382-6fbe60df912d

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryPolynomial.lean (solution of MIPRE.LowDegree.BinaryPolynomial.evalBits_xor);
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryPolynomial
open Cost
variable {R : Type*} [CommRing R]
theorem _root_.solution [CharP R 2] (z : R) (a b : BitStr) (hlen : a.length = b.length) :
    evalBits z (xorBits a b) = evalBits z a + evalBits z b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [xorBits]
  | cons x a ih =>
    cases b with
    | nil => simp at hlen
    | cons y b =>
      have hb : (ofBool (Bool.xor x y) : R) = ofBool x + ofBool y := by
        cases x <;> cases y <;> simp [ofBool, CharTwo.add_self_eq_zero]
      simp only [xorBits, List.zipWith_cons_cons, evalBits_cons, hb]
      have ht := ih b (by simpa using hlen)
      change evalBits z (List.zipWith Bool.xor a b) = _ at ht
      rw [ht]
      ring
end MIPRE.LowDegree.BinaryPolynomial
