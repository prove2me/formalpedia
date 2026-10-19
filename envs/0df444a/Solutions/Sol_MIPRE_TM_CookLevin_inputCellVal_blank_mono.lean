-- Prove2me | solution 1 for MIPRE.TM.CookLevin.inputCellVal_blank_mono
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:49:18.117219+00:00
-- url     : https://prove2.me/submissions/a142daec-b378-4e44-9c16-b7bedb8252d4

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Correct.lean (solution of MIPRE.TM.CookLevin.inputCellVal_blank_mono);
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
import Definitions.Def_MIPRE_TM_CookLevin_Correct
import Theorems.Thm_MIPRE_TM_CookLevin_not_isBdry_iff

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
open MultiTapeTM (moveInputPos)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
variable (chk : Circuit)
variable {G : ℕ}
omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
theorem _root_.solution (x : List Symbol) (p p' : Pos S) (h2 : 2 < (p : ℕ))
    (hnb' : ¬ p'.IsBdry) (hpp' : p < p') (h : inputCellVal x p = .blank) :
    inputCellVal x p' = .blank := by
  have hnb : ¬ p.IsBdry := by
    rw [not_isBdry_iff] at hnb' ⊢
    have := Fin.lt_def.mp hpp'
    omega
  rw [inputCellVal_eq x p hnb, if_pos (by omega)] at h
  rw [inputCellVal_eq x p' hnb', if_pos (by have := Fin.lt_def.mp hpp'; omega)]
  have hnone : x[(p : ℕ) - 3]? = none := by
    cases hx : x[(p : ℕ) - 3]? with
    | none => rfl
    | some s => rw [hx] at h; exact absurd h (by simp)
  rw [List.getElem?_eq_none_iff] at hnone
  rw [List.getElem?_eq_none (by have := Fin.lt_def.mp hpp'; omega)]
end MIPRE.TM.CookLevin
