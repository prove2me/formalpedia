-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Desc.decodeVar_fieldsOf_idxOf
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:27:58.655157+00:00
-- url     : https://prove2.me/submissions/843cb98c-de03-4406-9e73-a2f7497b1fdd

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Index.lean (solution of MIPRE.TM.CookLevin.Desc.decodeVar_fieldsOf_idxOf);
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
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_bitsOfNat_bitsVal
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_decodeVar_ans
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_decodeVar_encodeVar
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_length_encodeVar

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
theorem tape_eq_inl_of_lt (d : Tape 7 6) (h : tapeCode d < 7) : d = .inl ⟨tapeCode d, h⟩ := by
  rcases d with ⟨j, hj⟩ | ⟨j, hj⟩
  · rfl
  · simp [tapeCode] at h
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G T : ℕ)
theorem decodeVar_fieldsOf_bitsVal (v : TabVar 7 6 Sym Ctl (Sof e) G) :
    decodeVar e G (fieldsOf e G T (bitsOfNat (mOf e G) (bitsVal (encodeVar e G v)))) = some v := by
  rw [show mOf e G = (encodeVar e G v).length from (length_encodeVar e G v).symm,
    bitsOfNat_bitsVal, decodeVar_encodeVar]
end
end MIPRE.TM.CookLevin.Desc

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Desc
open Interp SAT Cost
variable (e G T : ℕ)
theorem _root_.solution (hT : T ≤ Sof e) (v : TabVar 7 6 Sym Ctl (Sof e) G) :
    decodeVar e G (fieldsOf e G T (bitsOfNat (mOf e G) (idxOf e G T v))) = some v := by
  cases v with
  | cell t d p v =>
    rw [idxOf]
    split_ifs with h
    · obtain ⟨ht, hd, hp3, hpT, hv⟩ := h
      have hj : ansIdx e T d p v < 4 * T := ansIdx_lt e T hT ⟨ht, hd, hp3, hpT, hv⟩
      obtain ⟨jt, p', hjt, hp', hdec⟩ := decodeVar_ans e G T hT hj
      rw [hdec]
      have hpar : (if v = CellVal.sym Sym.one then 1 else 0) < 2 := by split_ifs <;> omega
      have hlt : (ansIdx e T d p v < 2 * T) ↔ tapeCode d = 5 := by
        unfold ansIdx
        constructor
        · intro hle
          by_contra hne
          rw [if_neg hne] at hle
          omega
        · intro h5
          rw [if_pos h5]
          omega
      have hr : rOf T (ansIdx e T d p v) = 2 * ((p : ℕ) - 3) +
          (if v = CellVal.sym Sym.one then 1 else 0) := by
        unfold rOf
        by_cases h5 : tapeCode d = 5
        · rw [if_pos (hlt.mpr h5)]
          unfold ansIdx
          rw [if_pos h5]
          omega
        · rw [if_neg (by simp only [hlt]; exact h5)]
          unfold ansIdx
          rw [if_neg h5]
          omega
      have hti : tapeIdx T (ansIdx e T d p v) = tapeCode d := by
        unfold tapeIdx
        by_cases h5 : tapeCode d = 5
        · rw [if_pos (hlt.mpr h5), h5]
        · rw [if_neg (by simp only [hlt]; exact h5)]
          rcases hd with h | h
          · exact absurd h h5
          · exact h.symm
      have hd' : (.inl jt : Tape 7 6) = d := by
        have hjt' : (jt : ℕ) = tapeCode d := by rw [hjt, hti]
        rw [tape_eq_inl_of_lt d (by rw [← hjt']; exact jt.isLt)]
        congr 1
        exact Fin.ext hjt'
      have hp'' : p' = p := by
        apply Fin.ext
        rw [hp', hr]
        omega
      have hvv : valOf T (ansIdx e T d p v) = v := by
        unfold valOf
        rw [hr]
        rcases hv with rfl | rfl
        · rw [if_neg (by simp)]
        · rw [if_pos (by simp)]
      have ht0 : (0 : Fin (Sof e + 1)) = t := Fin.ext (by simp [ht])
      rw [hd', hp'', hvv, ht0]
    · exact decodeVar_fieldsOf_bitsVal e G T _
  | head t d p => exact decodeVar_fieldsOf_bitsVal e G T _
  | state t q => exact decodeVar_fieldsOf_bitsVal e G T _
  | emitOne t => exact decodeVar_fieldsOf_bitsVal e G T _
  | emitBad t => exact decodeVar_fieldsOf_bitsVal e G T _
  | emitted t => exact decodeVar_fieldsOf_bitsVal e G T _
  | aux t js g => exact decodeVar_fieldsOf_bitsVal e G T _
end MIPRE.TM.CookLevin.Desc
