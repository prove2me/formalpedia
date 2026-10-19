-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryPolynomial.polyOfBits_substituteArtinSchreierBits
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:47:06.221163+00:00
-- url     : https://prove2.me/submissions/697c16f6-2251-4da3-84e2-ad892c4c05e8

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryArtinSchreierProg.lean (solution of MIPRE.LowDegree.BinaryPolynomial.polyOfBits_substituteArtinSchreierBits);
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierProg
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_eval2_polyOfBits
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_xor

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
/-- The Horner step has its stated semantics in every characteristic-two ring. -/
theorem evalBits_artinSchreierStep {R : Type*} [CommRing R] [CharP R 2]
    (z : R) (a : BitStr) (b : Bool) :
    evalBits z (artinSchreierStep a b) = ofBool b + (z ^ 2 + z) * evalBits z a := by
  rw [artinSchreierStep, evalBits_cons, evalBits_xor z _ _ (by simp)]
  simp only [evalBits_cons, evalBits_append, evalBits_nil, ofBool, Bool.false_eq_true,
    ↓reduceIte, mul_zero, add_zero, zero_add]
  ring
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
theorem evalBits_substituteArtinSchreierBits {R : Type*} [CommRing R] [CharP R 2]
    (z : R) (a : BitStr) :
    evalBits z (substituteArtinSchreierBits a) = evalBits (z ^ 2 + z) a := by
  rw [substituteArtinSchreierBits, evalBits_normalizeBits]
  induction a with
  | nil => rfl
  | cons b a ih =>
    simp only [List.foldr_cons, evalBits_artinSchreierStep, evalBits_cons, ih]
end
end MIPRE.LowDegree.BinaryPolynomial

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryPolynomial
open Cost Cost.PolyTimeFun Polynomial
theorem _root_.solution (a : BitStr) :
    polyOfBits (substituteArtinSchreierBits a) = (polyOfBits a).comp (X ^ 2 + X) := by
  rw [polyOfBits_eq_evalBits, evalBits_substituteArtinSchreierBits]
  exact (eval2_polyOfBits Polynomial.C (X ^ 2 + X) a).symm
end MIPRE.LowDegree.BinaryPolynomial
