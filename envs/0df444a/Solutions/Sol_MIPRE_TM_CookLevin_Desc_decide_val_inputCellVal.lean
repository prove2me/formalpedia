-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Desc.decide_val_inputCellVal
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:27:59.420696+00:00
-- url     : https://prove2.me/submissions/e0d47c1f-0848-48f5-82f8-588cdf2a8af3

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Sat.lean (solution of MIPRE.TM.CookLevin.Desc.decide_val_inputCellVal);
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
import Definitions.Def_MIPRE_TM_CookLevin_Describer
import Definitions.Def_MIPRE_TM_CookLevin_Semantics
import Definitions.Def_MIPRE_TM_CookLevin_Correct
import Definitions.Def_MIPRE_TM_CookLevin_Sound
import Definitions.Def_MIPRE_TM_CookLevin_Sat

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
/-- Boundary cells, numerically. -/
theorem isBdry_iff {S : ℕ} (p : Pos S) : p.IsBdry ↔ (p : ℕ) < 2 ∨ 2 * S + 5 ≤ p := by
  unfold Pos.IsBdry numCells
  omega
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem getElem_bits (l : BitStr) (k : ℕ) (h : k < (bits l).length) :
    (bits l)[k] = if l[k]'(by simpa using h) then Sym.one else Sym.zero :=
  List.getElem_map _
end
end MIPRE.TM.CookLevin.Desc

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Desc
open Interp SAT Cost Fml
theorem _root_.solution (e : ℕ) (ap : BitStr) (k : ℕ) {p : Pos (Sof e)}
    (hp : (p : ℕ) = k / 2 + 3) (hk : k < 2 * Sof e) :
    decide ((if k % 2 = 1 then CellVal.sym Sym.one else CellVal.blank) =
      inputCellVal (bits ap) p) = tapeBits ap k := by
  obtain ⟨pv, hpv⟩ := p
  subst hp
  have hnb : ¬ Pos.IsBdry (⟨k / 2 + 3, hpv⟩ : Pos (Sof e)) := by
    rw [isBdry_iff]
    simp only [Fin.val_mk]
    omega
  have hval : inputCellVal (bits ap) (⟨k / 2 + 3, hpv⟩ : Pos (Sof e)) =
      (ap[k / 2]?).elim CellVal.blank fun c => CellVal.sym (if c then Sym.one else Sym.zero) := by
    rw [inputCellVal, if_neg hnb]
    simp only [Fin.val_mk, Nat.add_sub_cancel]
    by_cases hin : k / 2 < ap.length
    · rw [dif_pos (show 3 ≤ k / 2 + 3 ∧ k / 2 < (bits ap).length from
        ⟨by omega, by simpa using hin⟩), List.getElem?_eq_getElem hin, getElem_bits]
      rfl
    · rw [dif_neg (show ¬ (3 ≤ k / 2 + 3 ∧ k / 2 < (bits ap).length) by
        rw [length_bits]; omega), List.getElem?_eq_none (by omega)]
      rfl
  rw [hval, tapeBits]
  by_cases hodd : k % 2 = 1
  · rw [if_pos hodd, if_neg (by omega : ¬ k % 2 = 0)]
    rcases hh : ap[k / 2]? with _ | c
    · simp [cellBits]
    · cases c <;> simp [cellBits]
  · rw [if_neg hodd, if_pos (by omega : k % 2 = 0)]
    rcases hh : ap[k / 2]? with _ | c
    · simp [cellBits]
    · cases c <;> simp [cellBits]
end MIPRE.TM.CookLevin.Desc
