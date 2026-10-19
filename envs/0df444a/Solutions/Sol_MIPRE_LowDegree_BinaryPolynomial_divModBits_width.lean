-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryPolynomial.divModBits_width
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:47:07.425414+00:00
-- url     : https://prove2.me/submissions/c9e07d01-ebe5-4b24-87de-285c77599550

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryDivision.lean (solution of MIPRE.LowDegree.BinaryPolynomial.divModBits_width);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_shiftReduce

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
/-- Normalizing cannot increase the coefficient width. -/
theorem length_normalizeStep_le (a : BitStr) (b : Bool) :
    (normalizeStep a b).length ≤ a.length + 1 := by
  cases b <;> simp [normalizeStep]
  split <;> simp
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
/-- The normalized representation is no longer than its input. -/
theorem length_normalizeBits_le (a : BitStr) : (normalizeBits a).length ≤ a.length := by
  induction a with
  | nil => simp
  | cons b a ih =>
    rw [normalizeBits_cons]
    have hs := length_normalizeStep_le (normalizeBits a) b
    simp only [List.length_cons]
    omega
end
end MIPRE.LowDegree.BinaryPolynomial

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
theorem _root_.solution (p a : BitStr) :
    (divModBits p a).1.length ≤ a.length ∧ (divModBits p a).2.length ≤ p.length := by
  unfold divModBits
  split
  · exact ⟨length_normalizeBits_le a, Nat.zero_le _⟩
  · have hw := divisionFold_width p a
    exact ⟨(length_normalizeBits_le _).trans hw.2.1.le,
      (length_normalizeBits_le _).trans hw.2.2.le⟩
end MIPRE.LowDegree.BinaryPolynomial
