-- Prove2me | solution 1 for MIPRE.TM.CookLevin.freeClauses_sat
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:50:23.309532+00:00
-- url     : https://prove2.me/submissions/994d4e53-7ee7-4036-bde3-17d46e17d966

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Correct.lean (solution of MIPRE.TM.CookLevin.freeClauses_sat);
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
import Theorems.Thm_MIPRE_TM_CookLevin_inputCellVal_blank_mono
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

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos moveInputPos_zero)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
variable (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
theorem inputCellVal_bdry_iff (x : List Symbol) (p : Pos S) :
    inputCellVal x p = .bdry ↔ p.IsBdry := by
  unfold inputCellVal
  split_ifs <;> simp_all
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem cfgAt_zero' : cfgAt M (input := input) ((0 : Fin (S + 1)) : ℕ) = M.initCfg input :=
  configs_zero
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
variable (chk : Circuit)
variable {G : ℕ}
omit [Fintype Symbol] [Fintype State] [DecidableEq Symbol] [DecidableEq State] in
theorem unit_eval (f : TabVar i w Symbol State S G → Bool) (v : TabVar i w Symbol State S G)
    (b : Bool) : (unit v b).eval f = true ↔ f v = b := by
  cases b <;> cases h : f v <;> simp [unit, cl, Clause3.eval, Lit.eval, h]
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
variable (chk : Circuit)
variable {G : ℕ}
omit [Fintype Symbol] [Fintype State] [DecidableEq Symbol] [DecidableEq State] in
theorem imp2_eval (f : TabVar i w Symbol State S G → Bool) (a b : TabVar i w Symbol State S G) :
    (imp2 a b).eval f = true ↔ (f a = true → f b = true) := by
  cases ha : f a <;> cases hb : f b <;> simp [imp2, cl, Clause3.eval, Lit.eval, ha, hb]
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
variable (chk : Circuit)
variable {G : ℕ}
omit [Fintype Symbol] [Fintype State] [DecidableEq Symbol] [DecidableEq State] in
theorem nand2_eval (f : TabVar i w Symbol State S G → Bool) (a b : TabVar i w Symbol State S G) :
    (nand2 a b).eval f = true ↔ ¬ (f a = true ∧ f b = true) := by
  cases ha : f a <;> cases hb : f b <;> simp [nand2, cl, Clause3.eval, Lit.eval, ha, hb]
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
variable (chk : Circuit)
variable {G : ℕ}
omit [Fintype Symbol] [Fintype State] [DecidableEq Symbol] [DecidableEq State] in
theorem cl_eval (f : TabVar i w Symbol State S G → Bool) (l₁ l₂ l₃ : Lit (TabVar i w Symbol State S G)) :
    (cl l₁ l₂ l₃).eval f = true ↔ l₁.eval f = true ∨ l₂.eval f = true ∨ l₃.eval f = true := by
  simp [cl, Clause3.eval, or_assoc]
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
variable (chk : Circuit)
variable {G : ℕ}
omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
theorem cellValAt_inl (c : Cfg i w Symbol State input) (j : Fin i) (p : Pos S) :
    cellValAt (S := S) c (.inl j) p = inputCellVal (input j) p := rfl
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
variable (chk : Circuit)
variable {G : ℕ}
omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
/-- An interior input cell holds a blank or a symbol of the string. -/
theorem inputCellVal_mem (x : List Symbol) (p : Pos S) (hnb : ¬ p.IsBdry) :
    inputCellVal x p = .blank ∨
      ∃ (k : ℕ) (hk : k < x.length), (p : ℕ) = k + 3 ∧ inputCellVal x p = .sym x[k] := by
  rw [inputCellVal_eq x p hnb]
  by_cases h3 : 3 ≤ (p : ℕ)
  · rw [if_pos h3]
    by_cases hl : (p : ℕ) - 3 < x.length
    · right
      refine ⟨(p : ℕ) - 3, hl, by omega, ?_⟩
      rw [List.getElem?_eq_getElem hl]
    · left
      rw [List.getElem?_eq_none (by omega)]
  · left; rw [if_neg h3]
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
variable (chk : Circuit)
variable {G : ℕ}
omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
/-- Cell `2` of an input tape is blank. -/
theorem inputCellVal_two (x : List Symbol) :
    inputCellVal (S := S) x ⟨2, by unfold numCells; omega⟩ = .blank := by
  have hnb : ¬ Pos.IsBdry (S := S) ⟨2, by unfold numCells; omega⟩ := by
    rw [not_isBdry_iff]; simp [numCells]
  rw [inputCellVal_eq x _ hnb, if_neg (by simp)]
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
variable (s₀ s₁ : Symbol) (fixed : Fin i → Option (List Symbol))
theorem _root_.solution (hfree : ∀ j, fixed j = none → ∀ s ∈ input j, s = s₀ ∨ s = s₁) :
    (freeClauses (S := S) (G := chk.gates.length) s₀ s₁ fixed).Sat
      (runAssign M acc (input := input) chk) := by
  rintro c (((((⟨j, p, v, hj, hb, rfl⟩ | ⟨j, p, v, hj, hnb, h0, h1, hbl, rfl⟩) | ⟨j, v, hj, rfl⟩) |
    ⟨j, p, hj, hnb, rfl⟩) | ⟨j, p, v, v', hj, hnb, hvv', rfl⟩) | ⟨j, p, p', hj, h2, hnb', hpp', rfl⟩)
  · rw [unit_eval, runAssign_cell]
    simp only [baseAssign]
    rw [cfgAt_zero', cellValAt_inl, (inputCellVal_bdry_iff _ _).mpr hb]
    apply decide_eq_decide.mpr
    exact eq_comm
  · rw [unit_eval, runAssign_cell]
    simp only [baseAssign]
    rw [cfgAt_zero', cellValAt_inl]
    apply decide_eq_false
    intro h
    rcases inputCellVal_mem (input j) p hnb with h' | ⟨k, hk, -, h'⟩
    · exact hbl (h.symm.trans h')
    · rcases hfree j hj _ (List.getElem_mem hk) with hs | hs
      · exact h0 (by rw [← h, h', hs])
      · exact h1 (by rw [← h, h', hs])
  · rw [unit_eval, runAssign_cell]
    simp only [baseAssign]
    rw [cfgAt_zero', cellValAt_inl, inputCellVal_two]
    apply decide_eq_decide.mpr
    exact eq_comm
  · rw [cl_eval]
    simp only [lit_eval_true, runAssign_cell, baseAssign]
    rw [cfgAt_zero', cellValAt_inl]
    simp only [decide_eq_true_iff]
    rcases inputCellVal_mem (input j) p hnb with h' | ⟨k, hk, -, h'⟩
    · exact Or.inr (Or.inr h')
    · rcases hfree j hj _ (List.getElem_mem hk) with hs | hs
      · exact Or.inl (by rw [h', hs])
      · exact Or.inr (Or.inl (by rw [h', hs]))
  · rw [nand2_eval]
    simp only [runAssign_cell, baseAssign]
    rw [cfgAt_zero', cellValAt_inl]
    simp only [decide_eq_true_iff]
    rintro ⟨h, h'⟩
    exact hvv' (h.symm.trans h')
  · rw [imp2_eval]
    simp only [runAssign_cell, baseAssign]
    rw [cfgAt_zero', cellValAt_inl]
    simp only [decide_eq_true_iff]
    exact inputCellVal_blank_mono (input j) p p' h2 hnb' hpp'
end MIPRE.TM.CookLevin
