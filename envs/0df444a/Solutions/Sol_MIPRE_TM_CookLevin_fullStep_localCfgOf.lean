-- Prove2me | solution 1 for MIPRE.TM.CookLevin.fullStep_localCfgOf
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:50:30.854981+00:00
-- url     : https://prove2.me/submissions/5688cfc8-96fe-4d0c-b117-de1bf48ad858

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

/-
Vendored from CSLib (https://github.com/leanprover/cslib), upstream file
  Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean
at commit 3aa9d4416c185e0b9faeb72bbd65abe85b95dbcc (2026-08-03); fetched 2026-08-05.

CSLib cannot currently be a Lake dependency of this project: its MultiTape development
requires Lean >= v4.33.0-rc1, while this project pins v4.32.0. See
`planning/tm-infrastructure.md` (decision D1). Delete this copy and `require` CSLib once
the toolchains align.

Adaptations (the only differences from upstream):
* module-system markers removed: the `module` line, `public import` -> `import`, and the
  `@[expose] public section` line (replaced by the `set_option` lines below);
* `set_option autoImplicit true` / `set_option relaxedAutoImplicit true` added to restore
  the upstream Lean defaults (this project's lakefile disables both);
* the `RelatesInSteps` import redirected to the vendored copy (`MIPRE.Cslib...`);
* `open Cslib Relation` -> `open Relation` (the `Cslib` namespace is not vendored).
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Semantics.lean (solution of MIPRE.TM.CookLevin.fullStep_localCfgOf);
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
import Theorems.Thm_MIPRE_TM_CookLevin_HeadsIn_headCell_bounds
import Theorems.Thm_MIPRE_TM_CookLevin_not_isBdry_iff
import Theorems.Thm_MIPRE_TM_CookLevin_toOpt_inputCellVal_headCell

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace Turing.MultiTapeTM
section
open Relation
set_option autoImplicit true
set_option relaxedAutoImplicit true
variable {k : ℕ} {State Symbol : Type*}
variable {tm : MultiTapeTM k Symbol State}
/-- A left move away from the left input boundary decrements the native input position. -/
lemma moveInputPos_neg_of_ne_left {n : ℕ} (p : Fin (n + 2)) (h : p ≠ 0) :
    moveInputPos p .neg = ⟨p.val - 1, by have := p.isLt; omega⟩ := by
  have hp : 0 < p.val := Nat.pos_of_ne_zero (fun hz => h (Fin.ext hz))
  unfold moveInputPos
  apply Fin.ext
  rw [dif_pos] <;> simp <;> omega
end
end Turing.MultiTapeTM

namespace Turing.MultiTapeTM
section
open Relation
set_option autoImplicit true
set_option relaxedAutoImplicit true
variable {k : ℕ} {State Symbol : Type*}
variable {tm : MultiTapeTM k Symbol State}
/-- A right move away from the right input boundary increments the native input position. -/
lemma moveInputPos_pos_of_ne_right {n : ℕ} (p : Fin (n + 2)) (h : p.val ≠ n + 1) :
    moveInputPos p .pos = ⟨p.val + 1, by have := p.isLt; omega⟩ := by
  unfold moveInputPos
  rw [dif_pos]
  · apply Fin.ext
    simp
  · simp
    omega
end
end Turing.MultiTapeTM

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos moveInputPos_zero moveInputPos_neg_of_ne_left moveInputPos_pos_of_ne_right)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
variable (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
theorem step_state (c : Cfg i w Symbol State input) {q : State} (hst : c.state = some q) :
    (M.step c).state = (M.tr q c.inputSymbols c.workTapeSymbols).q' := by
  unfold step; rw [hst]
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos moveInputPos_zero moveInputPos_neg_of_ne_left moveInputPos_pos_of_ne_right)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
variable (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
theorem step_inputPos (c : Cfg i w Symbol State input) {q : State} (hst : c.state = some q)
    (j : Fin i) : (M.step c).inputPos j =
      moveInputPos (c.inputPos j) ((M.tr q c.inputSymbols c.workTapeSymbols).inputMoves j) := by
  unfold step; rw [hst]
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos moveInputPos_zero moveInputPos_neg_of_ne_left moveInputPos_pos_of_ne_right)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
variable (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
theorem step_workTapePos (c : Cfg i w Symbol State input) {q : State} (hst : c.state = some q)
    (j : Fin w) : (M.step c).workTapePos j =
      c.workTapePos j + ((M.tr q c.inputSymbols c.workTapeSymbols).workActions j).2 := by
  unfold step; rw [hst]
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos moveInputPos_zero moveInputPos_neg_of_ne_left moveInputPos_pos_of_ne_right)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
variable (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
theorem step_workTapes (c : Cfg i w Symbol State input) {q : State} (hst : c.state = some q)
    (j : Fin w) : (M.step c).workTapes j =
      match ((M.tr q c.inputSymbols c.workTapeSymbols).workActions j).1 with
      | none => c.workTapes j
      | some s => Function.update (c.workTapes j) (c.workTapePos j) s := by
  unfold step; rw [hst]; rfl
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos moveInputPos_zero moveInputPos_neg_of_ne_left moveInputPos_pos_of_ne_right)
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
open MultiTapeTM (moveInputPos moveInputPos_zero moveInputPos_neg_of_ne_left moveInputPos_pos_of_ne_right)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
variable (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
theorem inputCellVal_ne_bdry (x : List Symbol) (p : Pos S) (hnb : ¬ p.IsBdry) :
    inputCellVal x p ≠ .bdry := by
  unfold inputCellVal
  rw [if_neg hnb]
  split_ifs <;> simp
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos moveInputPos_zero moveInputPos_neg_of_ne_left moveInputPos_pos_of_ne_right)
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
open MultiTapeTM (moveInputPos moveInputPos_zero moveInputPos_neg_of_ne_left moveInputPos_pos_of_ne_right)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
variable (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
theorem cellValAt_inr (c : Cfg i w Symbol State input) (j : Fin w) (p : Pos S) (hnb : ¬ p.IsBdry) :
    cellValAt (S := S) c (.inr j) p = .ofOpt (c.workTapes j ((p : ℤ) - (S + 3))) := by
  simp [cellValAt, hnb]
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos moveInputPos_zero moveInputPos_neg_of_ne_left moveInputPos_pos_of_ne_right)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
variable (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem moveInputPos_neg_zero {n : ℕ} : moveInputPos (0 : Fin (n + 2)) .neg = 0 := by
  apply Fin.ext
  simp [moveInputPos, SignType.cast]
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos moveInputPos_zero moveInputPos_neg_of_ne_left moveInputPos_pos_of_ne_right)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
variable (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem moveInputPos_pos_right {n : ℕ} (p : Fin (n + 2)) (h : (p : ℕ) = n + 1) :
    moveInputPos p .pos = p := by
  apply Fin.ext
  unfold moveInputPos
  rw [dif_neg (by simp [SignType.cast]; omega)]
  simp [h]
end
end MIPRE.TM.CookLevin

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos moveInputPos_zero moveInputPos_neg_of_ne_left moveInputPos_pos_of_ne_right)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
variable (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
theorem _root_.solution (c : Cfg i w Symbol State input) (js : Tape i w → Center S)
    (hin : HeadsIn c S) (δ : Tape i w → Fin 5)
    (hδ : ∀ d, 1 ≤ (δ d : ℕ) ∧ (δ d : ℕ) ≤ 3 ∧ (localCfgOf M acc c js).HeadAt d (δ d)) :
    FullStep M acc (localCfgOf M acc c js) δ := by
  -- the head of every tape is at the cell `js d + δ d`
  have hhead : ∀ d, headCell (S := S) c d = (js d : ℤ) + (δ d : ℕ) := by
    intro d
    have h := (hδ d).2.2 (δ d)
    simp only [localCfgOf, cellIdx_val, decide_true] at h
    have h' := of_decide_eq_true h
    push_cast at h'
    exact h'
  have hbd := fun d => hin.headCell_bounds (S := S) d
  cases hst : c.state with
  | none =>
    simp only [FullStep, localCfgOf, hst]
    refine ⟨fun d => ?_, fun d => ?_, ?_, ?_, ?_⟩
    · rw [step_of_halt hst]; rfl
    · rw [step_of_halt hst]; rfl
    · rw [step_of_halt hst, hst]
    · simp [outputSymbol, hst]
    · simp [outputSymbol, hst]
  | some q =>
    simp only [FullStep, localCfgOf, hst]
    have hnb : ∀ d, ¬ (cellIdx (js d) (δ d) : Pos S).IsBdry := by
      intro d
      rw [not_isBdry_iff]
      have := hbd d
      have := hhead d
      simp only [cellIdx_val]; omega
    -- the cells under the heads carry the symbols the machine reads
    have hcell_in : ∀ j, (cellValAt (S := S) c (.inl j) (cellIdx (js (.inl j)) (δ (.inl j)))).toOpt =
        c.inputSymbol j := by
      intro j
      have := hhead (.inl j)
      simp only [headCell] at this
      exact toOpt_inputCellVal_headCell c j _ (by simp only [cellIdx_val]; omega)
        (hnb (.inl j))
    have hcell_wk : ∀ j, (cellValAt (S := S) c (.inr j) (cellIdx (js (.inr j)) (δ (.inr j)))).toOpt =
        c.workTapeSymbols j := by
      intro j
      rw [cellValAt_inr c j _ (hnb _), CellVal.toOpt_ofOpt]
      have := hhead (.inr j)
      simp only [headCell] at this
      simp only [Cfg.workTapeSymbols]
      congr 1
      simp only [cellIdx_val]
      push_cast at this ⊢; omega
    have hin' : (fun j => (cellValAt (S := S) c (.inl j) (cellIdx (js (.inl j)) (δ (.inl j)))).toOpt) =
        c.inputSymbols := funext hcell_in
    have hwk' : (fun j => (cellValAt (S := S) c (.inr j) (cellIdx (js (.inr j)) (δ (.inr j)))).toOpt) =
        c.workTapeSymbols := funext hcell_wk
    refine ⟨fun d => ?_, ?_⟩
    · -- no head on a boundary cell
      cases d with
      | inl j => exact inputCellVal_ne_bdry _ _ (hnb _)
      | inr j => rw [cellValAt_inr c j _ (hnb _)]; cases c.workTapes j _ <;> simp [CellVal.ofOpt]
    simp only [hin', hwk']
    have hcnb : ∀ d, ¬ (center (js d) : Pos S).IsBdry := by
      intro d; rw [not_isBdry_iff]; have := (js d).isLt; have hnc : numCells S = 2 * S + 7 := rfl
      simp only [center_val]; omega
    refine ⟨fun j => rfl, fun j => ?_, fun j => ?_, fun j => ?_, step_state M c hst, ?_, ?_⟩
    · -- work cells
      rw [cellValAt_inr _ j _ (hcnb _), step_workTapes M c hst,
        cellValAt_inr c j (cellIdx (js (.inr j)) 2) (hcnb (.inr j))]
      have hh := hhead (.inr j)
      simp only [headCell] at hh
      by_cases h2 : δ (.inr j) = 2
      · rw [if_pos h2]
        have hpos : ((center (js (.inr j)) : Pos S) : ℤ) - (S + 3) = c.workTapePos j := by
          simp only [center_val]; rw [h2] at hh; simp only [Fin.val_two] at hh; push_cast at hh ⊢; omega
        cases ((M.tr q c.inputSymbols c.workTapeSymbols).workActions j).1 with
        | none => rfl
        | some s =>
          simp only
          rw [hpos, Function.update_self]
      · rw [if_neg h2]
        cases ((M.tr q c.inputSymbols c.workTapeSymbols).workActions j).1 with
        | none => rfl
        | some s =>
          simp only
          have hne : ((center (js (.inr j)) : Pos S) : ℤ) - (S + 3) ≠ c.workTapePos j := by
            simp only [center_val]
            push_cast at hh ⊢
            intro he
            apply h2
            apply Fin.ext
            simp only [Fin.val_two]
            omega
          rw [Function.update_of_ne hne]
          rfl
    · -- input heads
      have hh := hhead (.inl j)
      simp only [headCell] at hh
      have hlt := (c.inputPos j).isLt
      have hlen := hin.input_pos j
      have h1 := (hδ (.inl j)).1
      have h3 := (hδ (.inl j)).2.1
      simp only [headCell, step_inputPos M c hst, center_val, newOffset, true_and]
      -- the neighbor cell and the head cell
      have hnbr : cellValAt (S := S) c (.inl j) (cellIdx (js (.inl j)) ⟨(δ (.inl j) : ℕ) - 1, by omega⟩) = .bdry ↔
          (c.inputPos j : ℕ) = 0 := by
        show inputCellVal (S := S) (input j) _ = .bdry ↔ _
        rw [inputCellVal_bdry_iff, Pos.IsBdry]
        have hnc : numCells S = 2 * S + 7 := rfl
        simp only [cellIdx_val]
        omega
      have hself : cellValAt (S := S) c (.inl j) (cellIdx (js (.inl j)) (δ (.inl j))) = .blank ↔
          ((c.inputPos j : ℕ) = 0 ∨ (c.inputPos j : ℕ) = (input j).length + 1) := by
        show inputCellVal (S := S) (input j) _ = .blank ↔ _
        rw [inputCellVal_eq _ _ (hnb (.inl j))]
        have hp : ((cellIdx (js (.inl j)) (δ (.inl j)) : Pos S) : ℕ) = (c.inputPos j : ℕ) + 2 := by
          simp only [cellIdx_val]; omega
        rw [hp]
        by_cases h0 : (c.inputPos j : ℕ) = 0
        · rw [if_neg (by omega)]; simp [h0]
        · rw [if_pos (by omega)]
          have hidx : (c.inputPos j : ℕ) + 2 - 3 = (c.inputPos j : ℕ) - 1 := by omega
          rw [hidx]
          by_cases h1 : (c.inputPos j : ℕ) = (input j).length + 1
          · rw [List.getElem?_eq_none (by omega)]; simp [h1]
          · rw [List.getElem?_eq_getElem (by omega)]; simp [h0, h1]
      cases hm : (M.tr q c.inputSymbols c.workTapeSymbols).inputMoves j with
      | zero =>
        have hz : moveInputPos (c.inputPos j) SignType.zero = c.inputPos j := moveInputPos_zero _
        rw [hz]
        apply decide_eq_decide.mpr
        push_cast at hh ⊢; omega
      | neg =>
        dsimp only
        by_cases h0 : c.inputPos j = 0
        · have h0' : (c.inputPos j : ℕ) = 0 := by rw [h0]; rfl
          rw [h0, moveInputPos_neg_zero, if_pos (hnbr.mpr h0')]
          apply decide_eq_decide.mpr
          simp only [Fin.val_zero]
          rw [h0'] at hh
          push_cast at hh ⊢; omega
        · have h0' : (c.inputPos j : ℕ) ≠ 0 := fun h => h0 (Fin.ext h)
          rw [moveInputPos_neg_of_ne_left _ h0, if_neg (fun h => h0' (hnbr.mp h))]
          apply decide_eq_decide.mpr
          push_cast at hh ⊢; omega
      | pos =>
        dsimp only
        by_cases hr : (c.inputPos j : ℕ) = (input j).length + 1
        · rw [moveInputPos_pos_right _ hr, if_pos ⟨hself.mpr (Or.inr hr), fun h => by
            have := hnbr.mp h; omega⟩]
          apply decide_eq_decide.mpr
          push_cast at hh ⊢; omega
        · rw [moveInputPos_pos_of_ne_right _ hr]
          rw [if_neg]
          · apply decide_eq_decide.mpr
            push_cast at hh ⊢; omega
          · rintro ⟨hb, hnb'⟩
            rcases hself.mp hb with h0 | h0
            · exact hnb' (hnbr.mpr h0)
            · exact hr h0
    · -- work heads
      have hh := hhead (.inr j)
      simp only [headCell] at hh
      simp only [headCell, step_workTapePos M c hst, center_val, newOffset]
      cases ((M.tr q c.inputSymbols c.workTapeSymbols).workActions j).2 <;>
        simp only [SignType.cast, Bool.false_eq_true, false_and, if_false] <;>
        apply decide_eq_decide.mpr <;> push_cast at hh ⊢ <;> omega
    · simp [outputSymbol, hst]
    · simp [outputSymbol, hst]
end MIPRE.TM.CookLevin
