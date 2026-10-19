-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryPolynomial.gcdStep_correct
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:43:20.397311+00:00
-- url     : https://prove2.me/submissions/50f5f8a4-a2b7-4622-a50e-e80be5d973ae

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryGCD.lean (solution of MIPRE.LowDegree.BinaryPolynomial.gcdStep_correct);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Content
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGCD
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_divisionFold

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
/-- Normalization preserves the polynomial itself. -/
theorem polyOfBits_normalizeBits (a : BitStr) :
    polyOfBits (normalizeBits a) = polyOfBits a := by
  simpa only [polyOfBits_eq_evalBits] using evalBits_normalizeBits (X : Polynomial (ZMod 2)) a
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
/-- A nonempty normalized list has a leading coefficient equal to one. -/
theorem normalizeBits_getLast (a : BitStr) :
    normalizeBits a = [] ∨ (normalizeBits a).getLastD false = true := by
  induction a with
  | nil => exact Or.inl rfl
  | cons b a ih =>
    rcases ih with h | h
    · cases b <;> simp [normalizeBits_cons, normalizeStep, h]
    · have hn : normalizeBits a ≠ [] := by intro he; simp [he] at h
      cases ha : normalizeBits a with
      | nil => exact (hn ha).elim
      | cons c a =>
        cases b <;> simpa [normalizeBits_cons, normalizeStep, ha, List.getLastD_cons] using h
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
variable {R : Type*} [CommRing R] [CharP R 2]
/-- Monic division is correct as a polynomial identity, including division by one. -/
theorem polyOfBits_divModBits (p a : BitStr) :
    polyOfBits (p ++ [true]) * polyOfBits (divModBits p a).1 +
      polyOfBits (divModBits p a).2 = polyOfBits a := by
  by_cases hp : p = []
  · subst p
    change polyOfBits [true] * polyOfBits (normalizeBits a) + polyOfBits [] = _
    rw [polyOfBits_normalizeBits]
    simp [polyOfBits]
  · simp only [divModBits, List.isEmpty_eq_false_iff.mpr hp, Bool.false_eq_true, if_false]
    rw [polyOfBits_normalizeBits, polyOfBits_normalizeBits]
    simpa only [polyOfBits_eq_evalBits, evalBits_append, evalBits_cons, evalBits_nil,
      ofBool, if_true, mul_zero, add_zero, mul_one] using
      evalBits_divisionFold (X : Polynomial (ZMod 2)) p a hp
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Polynomial
/-- A list with a true leading bit decomposes into its lower coefficients and that bit. -/
theorem dropLast_append_true (a : BitStr) (h : a.getLastD false = true) :
    a.dropLast ++ [true] = a := by
  have hn : a ≠ [] := by intro he; simp [he] at h
  have hh : a.getLast hn = true := by
    cases a with
    | nil => exact (hn rfl).elim
    | cons b a => simpa only [List.getLast_eq_getLastD, List.getLastD_cons] using h
  simpa only [hh] using List.dropLast_append_getLast hn
end
end MIPRE.LowDegree.BinaryPolynomial

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryPolynomial
open Cost Cost.PolyTimeFun Polynomial
theorem _root_.solution (s : GCDState) (b : Bool)
    (hs : s.2 = [] ∨ s.2.getLastD false = true) :
    gcd (polyOfBits (gcdStep s b).1) (polyOfBits (gcdStep s b).2) =
      gcd (polyOfBits s.1) (polyOfBits s.2) ∧
    ((gcdStep s b).2 = [] ∨ (gcdStep s b).2.getLastD false = true) := by
  by_cases hz : s.2 = []
  · simp [gcdStep, hz]
  · have hlead : s.2.getLastD false = true := hs.resolve_left hz
    simp only [gcdStep, List.isEmpty_eq_false_iff.mpr hz, Bool.false_eq_true, if_false]
    refine ⟨?_, ?_⟩
    · have hdiv := polyOfBits_divModBits s.2.dropLast s.1
      rw [dropLast_append_true s.2 hlead] at hdiv
      have hd : polyOfBits s.2 ∣ polyOfBits s.1 - polyOfBits (divModBits s.2.dropLast s.1).2 := by
        refine ⟨polyOfBits (divModBits s.2.dropLast s.1).1, ?_⟩
        rw [← hdiv]
        ring
      rw [← gcd_eq_of_dvd_sub_right hd, gcd_comm]
    · unfold divModBits
      split
      · exact Or.inl rfl
      · exact normalizeBits_getLast _
end MIPRE.LowDegree.BinaryPolynomial
