-- Prove2me | solution 1 for MIPRE.TM.CookLevin.toOpt_inputCellVal_headCell
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:48:33.305496+00:00
-- url     : https://prove2.me/submissions/8c5b201b-bbc8-4d65-a0fc-04868bd25c32

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Semantics.lean (solution of MIPRE.TM.CookLevin.toOpt_inputCellVal_headCell);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Computability.Language
import Mathlib.Data.Finset.Max
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
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_CookLevin_Semantics

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos moveInputPos_zero)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
variable (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
/-- An interior input cell: the symbol of the input at index `p - 3`, if any, else a blank. -/
theorem inputCellVal_eq (x : List Symbol) (p : Pos S) (hnb : ¬ p.IsBdry) :
    inputCellVal x p =
      if 3 ≤ (p : ℕ) then
        (match x[(p : ℕ) - 3]? with
          | some s => CellVal.sym s
          | none => CellVal.blank)
      else .blank := by
  unfold inputCellVal
  rw [if_neg hnb]
  by_cases h3 : 3 ≤ (p : ℕ)
  · rw [if_pos h3]
    by_cases hl : (p : ℕ) - 3 < x.length
    · rw [dif_pos ⟨h3, hl⟩, List.getElem?_eq_getElem hl]
    · rw [dif_neg (fun h => hl h.2), List.getElem?_eq_none (by omega)]
  · rw [if_neg h3, dif_neg (fun h => h3 h.1)]
end
end MIPRE.TM.CookLevin

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos moveInputPos_zero)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
variable (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
theorem _root_.solution (c : Cfg i w Symbol State input) (j : Fin i) (p : Pos S)
    (hp : (p : ℕ) = (c.inputPos j : ℕ) + 2) (hnb : ¬ p.IsBdry) :
    (inputCellVal (input j) p).toOpt = c.inputSymbol j := by
  have hlt := (c.inputPos j).isLt
  rw [inputCellVal_eq (input j) p hnb]
  unfold Cfg.inputSymbol
  by_cases h0 : c.inputPos j = 0
  · have h0' : (c.inputPos j : ℕ) = 0 := by rw [h0]; rfl
    rw [dif_pos h0, if_neg (by omega)]
    rfl
  · have h0' : (c.inputPos j : ℕ) ≠ 0 := fun h => h0 (Fin.ext h)
    rw [dif_neg h0, if_pos (by omega)]
    have hidx : (p : ℕ) - 3 = (c.inputPos j : ℕ) - 1 := by omega
    rw [hidx]
    -- `c.inputPos j = (input j).length + 1` is an equality in `ℕ`, the coercion going left
    by_cases h1 : c.inputPos j = (input j).length + 1
    · rw [dif_pos h1, List.getElem?_eq_none (by omega)]
      rfl
    · rw [dif_neg h1, List.getElem?_eq_getElem (by omega)]
      rfl
end MIPRE.TM.CookLevin
