-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Desc.decodeVar_ans
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:26:14.00273+00:00
-- url     : https://prove2.me/submissions/cb943a02-a6b7-4736-b837-4cfccd560561

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Index.lean (solution of MIPRE.TM.CookLevin.Desc.decodeVar_ans);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Language
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_CookLevin_Layout
import Definitions.Def_MIPRE_TM_CookLevin_FieldFml
import Definitions.Def_MIPRE_TM_CookLevin_Kinds
import Definitions.Def_MIPRE_TM_CookLevin_Families
import Definitions.Def_MIPRE_TM_CookLevin_Window
import Definitions.Def_MIPRE_TM_CookLevin_FamilyFml
import Definitions.Def_MIPRE_TM_Interp_Tape
import Definitions.Def_MIPRE_TM_Interp_Reach
import Definitions.Def_MIPRE_TM_Interp_Routines
import Definitions.Def_MIPRE_TM_Interp_Repr
import Definitions.Def_MIPRE_TM_Interp_CopyTree
import Definitions.Def_MIPRE_TM_Interp_GetEnv
import Definitions.Def_MIPRE_TM_Interp_Desc
import Definitions.Def_MIPRE_TM_Interp_Step
import Definitions.Def_MIPRE_TM_Interp_InputRoutines
import Definitions.Def_MIPRE_TM_Interp_Run
import Definitions.Def_MIPRE_Foundations_SAT_Table
import Definitions.Def_MIPRE_TM_CookLevin_Params
import Definitions.Def_MIPRE_TM_CookLevin_AnsEnd
import Definitions.Def_MIPRE_TM_CookLevin_Index
import Theorems.Thm_MIPRE_SAT_bitsVal_take
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_bitsVal_bitsOfNat

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
/-- `S < 2^W` and `2S + 7 < 2^W`. -/
theorem numCells_lt_two_pow_W : numCells (Sof e) < 2 ^ W e := by
  unfold numCells Sof W
  rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]
  have := Nat.one_le_two_pow (n := e)
  omega
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem getD_bitsOfNat {w : ℕ} (n : ℕ) {i : ℕ} (hi : i < w) :
    (bitsOfNat w n).getD i false = n.testBit i := by
  rw [bitsOfNat, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hi]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem bitField_bitsOfNat_zero (w n k : ℕ) (hk : k ≤ w) :
    bitField (bitsOfNat w n) 0 k = n % 2 ^ k := by
  rw [bitField, List.drop_zero, bitsVal_take, bitsVal_bitsOfNat,
    Nat.mod_mod_of_dvd n (pow_dvd_pow 2 hk)]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G T : ℕ)
theorem tapeIdx_lt (j : ℕ) : tapeIdx T j < 7 := by unfold tapeIdx; split_ifs <;> omega
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G T : ℕ)
theorem rOf_lt (j : ℕ) (hj : j < 4 * T) : rOf T j < 2 * T := by
  unfold rOf; split_ifs <;> omega
end
end MIPRE.TM.CookLevin.Desc

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Desc
open Interp SAT Cost
variable (e G T : ℕ)
theorem _root_.solution (hT : T ≤ Sof e) {j : ℕ} (hj : j < 4 * T) :
    ∃ (jt : Fin 7) (p : Pos (Sof e)), (jt : ℕ) = tapeIdx T j ∧ (p : ℕ) = rOf T j / 2 + 3 ∧
      decodeVar e G (fieldsOf e G T (bitsOfNat (mOf e G) j)) =
        some (.cell 0 (.inl jt) p (valOf T j)) := by
  have hfl := four_T_le_flag e G T hT
  have hflm := flag_lt_m e G
  have hW := numCells_lt_two_pow_W e
  have hr : rOf T j < 2 * T := rOf_lt T j hj
  have hrd : rOf T j / 2 ≤ Sof e := by omega
  have hnc : numCells (Sof e) = 2 * Sof e + 7 := rfl
  -- the flag bit is clear
  have hflag : (bitsOfNat (mOf e G) j).getD (flagOff e G) false = false := by
    rw [getD_bitsOfNat _ hflm]
    exact Nat.testBit_eq_false_of_lt (by omega : j < 2 ^ flagOff e G)
  -- the value of the low bits
  have hj' : bitField (bitsOfNat (mOf e G) j) 0 (flagOff e G) = j := by
    rw [bitField_bitsOfNat_zero _ _ _ (by omega), Nat.mod_eq_of_lt (by omega)]
  -- the fields
  have hF : fieldsOf e G T (bitsOfNat (mOf e G) j) =
      { flag := false, tag := 0, t := 0, d := tapeIdx T j, p := (rOf T j / 2 + 3) % 2 ^ W e,
        v := if rOf T j % 2 = 1 then 1 else 5, q := 0, js := fun _ => 0, g := 0,
        ansOk := decide (j < 4 * T) } := by
    simp only [fieldsOf, hflag, Bool.false_eq_true, if_false, hj', rOf, tapeIdx]
    rfl
  have hp : (rOf T j / 2 + 3) % 2 ^ W e = rOf T j / 2 + 3 := Nat.mod_eq_of_lt (by omega)
  refine ⟨⟨tapeIdx T j, tapeIdx_lt T j⟩, ⟨rOf T j / 2 + 3, by omega⟩, rfl, rfl, ?_⟩
  rw [hF]
  simp only [decodeVar, Bool.false_eq_true, if_false, hp]
  rw [if_pos ⟨by simp [hj], trivial, trivial⟩, dif_pos ⟨tapeIdx_lt T j, by omega⟩]
  have hv : symOfCode (if rOf T j % 2 = 1 then 1 else 5) = some (valOf T j) := by
    unfold valOf
    split_ifs <;> rfl
  rw [hv]
end MIPRE.TM.CookLevin.Desc
