-- Prove2me | solution 1 for MIPRE.SAT.bitsVal_take
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:50:02.580798+00:00
-- url     : https://prove2.me/submissions/5587e8b3-9035-478e-a061-ffc8a0963287

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/FmlLib.lean (solution of MIPRE.SAT.bitsVal_take);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
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
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT
section
open Cost
theorem bitsVal_cons' (b : Bool) (l : BitStr) : bitsVal (b :: l) = 2 * bitsVal l + b.toNat := by
  rw [bitsVal_cons]; cases b <;> simp [Nat.bit]
end
end MIPRE.SAT

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT
open Cost
theorem _root_.solution (l : BitStr) (n : ℕ) : bitsVal (l.take n) = bitsVal l % 2 ^ n := by
  induction l generalizing n with
  | nil => simp [bitsVal_nil]
  | cons b l ih =>
    cases n with
    | zero => simp [bitsVal_nil, Nat.mod_one]
    | succ n =>
      rw [List.take_succ_cons, bitsVal_cons', bitsVal_cons', ih, Nat.pow_succ, Nat.mul_comm (2 ^ n) 2]
      have h2 : 0 < 2 ^ n := Nat.two_pow_pos n
      generalize bitsVal l = a
      obtain ⟨q, r, rfl, hr⟩ : ∃ q r, a = q * 2 ^ n + r ∧ r < 2 ^ n :=
        ⟨a / 2 ^ n, a % 2 ^ n, (Nat.div_add_mod' a (2 ^ n)).symm, Nat.mod_lt a h2⟩
      rw [Nat.add_comm (q * 2 ^ n) r, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
      cases b
      · simp only [Bool.toNat_false, Nat.add_zero]
        rw [show 2 * (r + q * 2 ^ n) = 2 * r + q * (2 * 2 ^ n) by ring, Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt (by omega)]
      · simp only [Bool.toNat_true]
        rw [show 2 * (r + q * 2 ^ n) + 1 = (2 * r + 1) + q * (2 * 2 ^ n) by ring,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
end MIPRE.SAT
