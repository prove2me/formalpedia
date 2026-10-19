-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryPolynomial.normalize_monic
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:45:51.094212+00:00
-- url     : https://prove2.me/submissions/db47fc80-8fa8-4dd2-8cf3-c91544c057b4

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryRepresentation.lean (solution of MIPRE.LowDegree.BinaryPolynomial.normalize_monic);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation

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
/-- A monic polynomial's leading coefficient is present in its coefficient list. -/
theorem natDegree_lt_length (l : BitStr) (h : (polyOfBits l).Monic) :
    (polyOfBits l).natDegree < l.length := by
  have hc : (polyOfBits l).coeff (polyOfBits l).natDegree = 1 := h.coeff_natDegree
  by_contra hn
  rw [coeff_polyOfBits] at hc
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega :
    l.length ≤ (polyOfBits l).natDegree), ofBool] at hc
end
end MIPRE.LowDegree.BinaryPolynomial

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryPolynomial
open Cost
theorem _root_.solution (l : BitStr) (h : (polyOfBits l).Monic) :
    polyOfBits (l.take (polyOfBits l).natDegree ++ [true]) = polyOfBits l := by
  let k := (polyOfBits l).natDegree
  have hk : k < l.length := natDegree_lt_length l h
  have htake : (l.take k).length = k := by simp [min_eq_left (by omega : k ≤ l.length)]
  ext i
  change (polyOfBits (l.take k ++ [true])).coeff i = (polyOfBits l).coeff i
  rw [coeff_polyOfBits]
  by_cases hi : i < k
  · rw [coeff_polyOfBits]
    congr 1
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt hi]
  · by_cases heq : i = k
    · subst i
      rw [h.coeff_natDegree]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), htake, Nat.sub_self]
      rfl
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : (polyOfBits l).natDegree < i)]
      have hlen : (l.take k ++ [true]).length ≤ i := by
        simp only [List.length_append, List.length_singleton]
        omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen, ofBool]
end MIPRE.LowDegree.BinaryPolynomial
