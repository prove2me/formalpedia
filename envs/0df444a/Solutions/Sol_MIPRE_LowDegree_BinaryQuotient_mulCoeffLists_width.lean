-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryQuotient.mulCoeffLists_width
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:44:58.687984+00:00
-- url     : https://prove2.me/submissions/c59ab5f0-3c9d-467e-bb00-73d8bb9bb218

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryQuotientPolynomial.lean (solution of MIPRE.LowDegree.BinaryQuotient.mulCoeffLists_width);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_mulReduce

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
/-- Addition keeps all correctly sized coefficients correctly sized. -/
theorem addCoeffLists_width (as bs : List BitStr) (n : ℕ)
    (ha : ∀ a ∈ as, a.length = n) (hb : ∀ b ∈ bs, b.length = n) :
    ∀ c ∈ addCoeffLists as bs, c.length = n := by
  induction as generalizing bs with
  | nil => exact hb
  | cons a as ih =>
    cases bs with
    | nil => exact ha
    | cons b bs =>
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · simp [ha a (by simp), hb b (by simp)]
      · exact ih bs (fun d hd => ha d (by simp [hd])) (fun d hd => hb d (by simp [hd])) c hc
end
end MIPRE.LowDegree.BinaryQuotient

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryQuotient
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R]
theorem _root_.solution (p : BitStr) (as bs : List BitStr)
    (ha : ∀ a ∈ as, a.length = p.length) :
    ∀ c ∈ mulCoeffLists p as bs, c.length = p.length := by
  induction as with
  | nil => simp [mulCoeffLists]
  | cons a as ih =>
    apply addCoeffLists_width
    · intro c hc
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
      exact length_mulReduce _ _ _ (ha a (by simp))
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact length_zeroBits p
      · exact ih (fun d hd => ha d (by simp [hd])) c hc
end MIPRE.LowDegree.BinaryQuotient
