-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryPolynomial.length_mulReduce_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:45:50.317981+00:00
-- url     : https://prove2.me/submissions/6a078a3c-2b17-4105-a380-a8bf42c0d85c

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryPolynomial.lean (solution of MIPRE.LowDegree.BinaryPolynomial.length_mulReduce_le);
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
theorem _root_.solution (p a b : BitStr) : (mulReduce p a b).length ≤ a.length := by
  induction b with
  | nil => simp [mulReduce]
  | cons bit b ih =>
    change (if bit then xorBits (shiftReduce p (mulReduce p a b)) a
      else shiftReduce p (mulReduce p a b)).length ≤ _
    split
    · rw [length_xorBits]
      exact (min_le_left _ _).trans ((length_shiftReduce_le _ _).trans ih)
    · exact (length_shiftReduce_le _ _).trans ih
end MIPRE.LowDegree.BinaryPolynomial
