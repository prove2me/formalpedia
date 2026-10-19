-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryPolynomial.evalBits_divisionFold
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:48:59.290011+00:00
-- url     : https://prove2.me/submissions/c9fdd68f-1209-43e7-924a-b4ab4dcaaadc

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryDivision.lean (solution of MIPRE.LowDegree.BinaryPolynomial.evalBits_divisionFold);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_divisionStep
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_shiftReduce

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
variable {R : Type*} [CommRing R] [CharP R 2]
/-- On well-formed states, a division step preserves the fixed remainder width. -/
theorem divisionStep_length (p q r : BitStr) (b : Bool) (hr : r.length = p.length) :
    (divisionStep (p, q, r) b).2.2.length = p.length := by
  cases b <;> simp [divisionStep, length_shiftReduce p r hr]
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
variable {R : Type*} [CommRing R] [CharP R 2]
/-- The right-fold state retains its modulus and its prescribed remainder width. -/
theorem divisionFold_width (p a : BitStr) :
    (divisionFold p a).1 = p ∧
    (divisionFold p a).2.1.length = a.length ∧
    (divisionFold p a).2.2.length = p.length := by
  induction a with
  | nil => simp [divisionFold]
  | cons b a ih =>
    change (divisionStep (divisionFold p a) b).1 = p ∧
      (divisionStep (divisionFold p a) b).2.1.length = (b :: a).length ∧
      (divisionStep (divisionFold p a) b).2.2.length = p.length
    refine ⟨ih.1, ?_, ?_⟩
    · simpa only [divisionStep, List.length_cons] using congrArg (· + 1) ih.2.1
    · exact (divisionStep_length _ _ _ b
        (ih.2.2.trans (congrArg List.length ih.1).symm)).trans (congrArg List.length ih.1)
end
end MIPRE.LowDegree.BinaryPolynomial

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryPolynomial
open Cost Cost.PolyTimeFun Polynomial
variable {R : Type*} [CommRing R] [CharP R 2]
theorem _root_.solution (z : R) (p a : BitStr) (hp : p ≠ []) :
    (evalBits z p + z ^ p.length) * evalBits z (divisionFold p a).2.1 +
      evalBits z (divisionFold p a).2.2 = evalBits z a := by
  induction a with
  | nil => simp [divisionFold]
  | cons b a ih =>
    have hw := divisionFold_width p a
    change (evalBits z p + z ^ p.length) *
      evalBits z (divisionStep (divisionFold p a) b).2.1 +
      evalBits z (divisionStep (divisionFold p a) b).2.2 = _
    have hs := evalBits_divisionStep z (divisionFold p a).1 (divisionFold p a).2.1
      (divisionFold p a).2.2 b (by simpa only [hw.1] using hp)
      (hw.2.2.trans (congrArg List.length hw.1).symm)
    change (evalBits z (divisionFold p a).1 + z ^ (divisionFold p a).1.length) *
      evalBits z (divisionStep (divisionFold p a) b).2.1 +
      evalBits z (divisionStep (divisionFold p a) b).2.2 = _ at hs
    rw [hw.1, ih] at hs
    exact hs
end MIPRE.LowDegree.BinaryPolynomial
