-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryQuotient.root_eq
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:43:31.550797+00:00
-- url     : https://prove2.me/submissions/11e78263-e459-4dfe-bc45-2fc07e9910a8

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryQuotient.lean (solution of MIPRE.LowDegree.BinaryQuotient.root_eq);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.AdjoinRoot
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotient
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_eval2_polyOfBits

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryQuotient
open Cost BinaryPolynomial
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
theorem _root_.solution (p : BitStr) (hpoly : f = polyOfBits (p ++ [true])) :
    AdjoinRoot.root f ^ p.length = evalBits (AdjoinRoot.root f) p := by
  nontriviality (AdjoinRoot f)
  let : CharP (AdjoinRoot f) 2 :=
    charP_of_injective_ringHom (AdjoinRoot.of f).injective 2
  have h : (polyOfBits (p ++ [true])).eval₂ (AdjoinRoot.of f) (AdjoinRoot.root f) = 0 := by
    rw [← hpoly]
    exact AdjoinRoot.eval₂_root f
  rw [eval2_polyOfBits, evalBits_append] at h
  simp only [evalBits_cons, evalBits_nil, ofBool, if_true, mul_zero, add_zero, mul_one] at h
  exact (CharTwo.add_eq_zero.mp h).symm
end MIPRE.LowDegree.BinaryQuotient
