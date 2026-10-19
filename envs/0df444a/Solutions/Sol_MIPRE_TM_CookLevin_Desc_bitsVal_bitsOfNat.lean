-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Desc.bitsVal_bitsOfNat
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:47:50.995036+00:00
-- url     : https://prove2.me/submissions/ae53398a-d050-4631-944b-91615846a4b9

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Layout.lean (solution of MIPRE.TM.CookLevin.Desc.bitsVal_bitsOfNat);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Language
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Relation
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_CookLevin_Layout

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

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem bitsOfNat_zero (i : ℕ) : bitsOfNat 0 i = [] := rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem bitsOfNat_succ (m i : ℕ) :
    bitsOfNat (m + 1) i = decide (i % 2 = 1) :: bitsOfNat m (i / 2) := by
  rw [bitsOfNat, List.ofFn_succ, bitsOfNat]
  congr 1
  · simp
  · congr 1
    funext k
    simp [Nat.testBit_succ]
end
end MIPRE.TM.CookLevin.Desc

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Desc
open Interp SAT Cost
theorem _root_.solution (m i : ℕ) : bitsVal (bitsOfNat m i) = i % 2 ^ m := by
  induction m generalizing i with
  | zero => simp [bitsOfNat_zero, bitsVal_nil, Nat.mod_one]
  | succ m ih =>
    rw [bitsOfNat_succ, bitsVal_cons', ih, Nat.pow_succ, Nat.mul_comm (2 ^ m) 2]
    have h2 : 0 < 2 ^ m := Nat.two_pow_pos m
    have hi := Nat.div_add_mod i 2
    have hlt := Nat.mod_lt i (show 0 < 2 by omega)
    obtain ⟨q, r, hqr, hr⟩ : ∃ q r, i / 2 = r + q * 2 ^ m ∧ r < 2 ^ m :=
      ⟨i / 2 / 2 ^ m, i / 2 % 2 ^ m, by rw [Nat.add_comm, Nat.div_add_mod'], Nat.mod_lt _ h2⟩
    rw [hqr, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
    have hb : (decide (i % 2 = 1)).toNat = i % 2 := by
      rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h]
    rw [hb]
    have hq : q * (2 * 2 ^ m) = 2 * (q * 2 ^ m) := by ring
    have : i = (2 * r + i % 2) + q * (2 * 2 ^ m) := by omega
    calc 2 * r + i % 2 = (2 * r + i % 2) % (2 * 2 ^ m) := (Nat.mod_eq_of_lt (by omega)).symm
      _ = ((2 * r + i % 2) + q * (2 * 2 ^ m)) % (2 * 2 ^ m) := (Nat.add_mul_mod_self_right _ _ _).symm
      _ = i % (2 * 2 ^ m) := by rw [← this]
end MIPRE.TM.CookLevin.Desc
