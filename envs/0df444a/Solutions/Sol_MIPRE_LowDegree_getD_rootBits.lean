-- Prove2me | solution 1 for MIPRE.LowDegree.getD_rootBits
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:27:30.797917+00:00
-- url     : https://prove2.me/submissions/96ca9c94-6231-422b-b13c-9f739c2f86e6

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinarySquareRoot.lean (solution of MIPRE.LowDegree.getD_rootBits);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySquareRoot

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree
section
open Cost
variable {α : Type*}
theorem getD_splitParity (l : List α) (fallback : α) (n : ℕ) :
    (splitParity l).1.getD n fallback = l.getD (2 * n) fallback ∧
    (splitParity l).2.getD n fallback = l.getD (2 * n + 1) fallback := by
  induction l generalizing n with
  | nil => simp [splitParity]
  | cons a l ih =>
    constructor
    · cases n with
      | zero => simp [splitParity]
      | succ n =>
        simpa [splitParity, Nat.mul_succ, Nat.add_assoc]
          using (ih n).2
    · simpa [splitParity] using (ih n).1
end
end MIPRE.LowDegree

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree
open Cost
variable {α : Type*}
theorem _root_.solution (l : List α) (fallback : α) (hodd : Odd l.length)
    {i : ℕ} (hi : i < l.length) :
    (rootBits l).getD i fallback = l.getD ((i + i) % l.length) fallback := by
  obtain ⟨r, hr⟩ := hodd
  have he : (splitParity l).1.length = r + 1 := by
    have := (length_splitParity l).1
    omega
  by_cases hsmall : i < r + 1
  · rw [rootBits, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega)]
    change (splitParity l).1.getD i fallback = _
    rw [(getD_splitParity l fallback i).1, Nat.mod_eq_of_lt (by omega), two_mul]
  · rw [rootBits, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega)]
    change (splitParity l).2.getD (i - (splitParity l).1.length) fallback = _
    rw [(getD_splitParity l fallback _).2, he]
    congr 1
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
end MIPRE.LowDegree
