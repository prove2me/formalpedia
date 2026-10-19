-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryQuotient.evalBits_eq_head_of_zero_or_one
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:43:48.862368+00:00
-- url     : https://prove2.me/submissions/d3029338-ec48-4d76-b515-8681279d2607

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryOrbitDescent.lean (solution of MIPRE.LowDegree.BinaryQuotient.evalBits_eq_head_of_zero_or_one);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_oneBits
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_toBits_ofBits

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost BinaryPolynomial
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
include hf in
/-- Equality in any monic quotient is faithful on fixed-width coefficient lists. -/
theorem evalBits_eq_iff (a b : BitStr)
    (ha : a.length = f.natDegree) (hb : b.length = f.natDegree) :
    evalBits (AdjoinRoot.root f) a = evalBits (AdjoinRoot.root f) b ↔ a = b := by
  rw [← ofBits_eq_evalBits f hf a ha, ← ofBits_eq_evalBits f hf b hb]
  constructor
  · intro h
    have he := congrArg (toBits f hf) h
    simpa only [toBits_ofBits f hf a ha, toBits_ofBits f hf b hb] using he
  · rintro rfl
    rfl
end
end MIPRE.LowDegree.BinaryQuotient

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryQuotient
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R]
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
include hf in
theorem _root_.solution (p c : BitStr)
    (hp : p.length = f.natDegree) (hc : c.length = f.natDegree) (hp0 : p ≠ [])
    (h : evalBits (AdjoinRoot.root f) c = 0 ∨ evalBits (AdjoinRoot.root f) c = 1) :
    evalBits (AdjoinRoot.root f) c = ofBool (c.headD false) := by
  rcases h with h | h
  · have he : c = zeroBits p := (evalBits_eq_iff f hf c (zeroBits p) hc
        ((length_zeroBits p).trans hp)).mp (by simpa using h)
    rw [he, evalBits_zeroBits]
    cases p <;> rfl
  · have he : c = oneBits p := (evalBits_eq_iff f hf c (oneBits p) hc
        ((length_oneBits p).trans hp)).mp (by rw [evalBits_oneBits _ p hp0]; exact h)
    rw [he, evalBits_oneBits _ p hp0]
    cases p with
    | nil => exact (hp0 rfl).elim
    | cons b bs => rfl
end MIPRE.LowDegree.BinaryQuotient
