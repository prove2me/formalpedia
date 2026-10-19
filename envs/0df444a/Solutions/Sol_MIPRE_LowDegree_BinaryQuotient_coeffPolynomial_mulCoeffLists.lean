-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryQuotient.coeffPolynomial_mulCoeffLists
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:46:25.845835+00:00
-- url     : https://prove2.me/submissions/4d7a3487-6612-499e-b7a4-dfd1e963d46f

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryQuotientPolynomial.lean (solution of MIPRE.LowDegree.BinaryQuotient.coeffPolynomial_mulCoeffLists);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotient
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientOrbit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitDescent
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientPolynomial
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_mulReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_mulReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_coeffPolynomial_addCoeffLists
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_mulCoeffLists_width

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R]
/-- Scalar multiplication has the expected polynomial interpretation. -/
theorem coeffPolynomial_scale [CharP R 2] (z : R) (p a : BitStr) (bs : List BitStr)
    (hz : z ^ p.length = evalBits z p) (ha : a.length = p.length) :
    coeffPolynomial z (bs.map (mulReduce p a)) = C (evalBits z a) * coeffPolynomial z bs := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.map_cons, coeffPolynomial_cons, evalBits_mulReduce z p a b ha hz, ih, map_mul]
    ring
end
end MIPRE.LowDegree.BinaryQuotient

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryQuotient
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R]
theorem _root_.solution [CharP R 2] (z : R) (p : BitStr) (as bs : List BitStr)
    (hz : z ^ p.length = evalBits z p) (ha : ∀ a ∈ as, a.length = p.length) :
    coeffPolynomial z (mulCoeffLists p as bs) = coeffPolynomial z as * coeffPolynomial z bs := by
  induction as with
  | nil => simp [mulCoeffLists]
  | cons a as ih =>
    have ha₀ := ha a (by simp)
    have ha₁ : ∀ b ∈ as, b.length = p.length := fun b hb => ha b (by simp [hb])
    rw [mulCoeffLists, coeffPolynomial_addCoeffLists z _ _ p.length]
    · rw [coeffPolynomial_scale z p a bs hz ha₀, coeffPolynomial_cons, evalBits_zeroBits,
        map_zero, zero_add, ih ha₁, coeffPolynomial_cons]
      ring
    · intro c hc
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
      exact length_mulReduce _ _ _ ha₀
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact length_zeroBits p
      · exact mulCoeffLists_width p as bs ha₁ c hc
end MIPRE.LowDegree.BinaryQuotient
