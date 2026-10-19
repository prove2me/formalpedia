-- Prove2me | solution 1 for MIPRE.TM.CookLevin.FreeFacts.cell_eq
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:28:45.285972+00:00
-- url     : https://prove2.me/submissions/403bae91-b6ed-441b-bf84-4cb40a1a72fb

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Sound.lean (solution of MIPRE.TM.CookLevin.FreeFacts.cell_eq);
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
import Definitions.Def_MIPRE_TM_CookLevin_Sound
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

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S G : ℕ}
omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem freeLen_spec (a : TabVar i w Symbol State S G → Bool) (j : Fin i) :
    blankBit a j (freeLen a j) = true ∨ numCells S ≤ freeLen a j + 5 :=
  Nat.find_spec (freeLen_exists a j)
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S G : ℕ}
omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem freeLen_min (a : TabVar i w Symbol State S G → Bool) (j : Fin i) {k : ℕ}
    (hk : k < freeLen a j) : ¬ (blankBit a j k = true ∨ numCells S ≤ k + 5) :=
  Nat.find_min (freeLen_exists a j) hk
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S G : ℕ}
omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem length_freeString (a : TabVar i w Symbol State S G → Bool) (j : Fin i) (s₀ s₁ : Symbol) :
    (freeString a j s₀ s₁).length = freeLen a j :=
  List.length_ofFn
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S G : ℕ}
variable (s₀ s₁ : Symbol)
variable {s₀ s₁}
omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
/-- An interior cell carrying one value carries no other. -/
theorem FreeFacts.onehot {a : TabVar i w Symbol State S G → Bool} {j : Fin i}
    (F : FreeFacts s₀ s₁ a j) (p : Pos S) (hnb : ¬ p.IsBdry) (u : CellVal Symbol)
    (hu : a (.cell 0 (.inl j) p u) = true) (v : CellVal Symbol) :
    a (.cell 0 (.inl j) p v) = decide (v = u) := by
  by_cases hv : v = u
  · subst hv; simp [hu]
  · rw [decide_eq_false hv]
    have := F.once p v u hnb hv
    cases h : a (.cell 0 (.inl j) p v)
    · rfl
    · exact absurd ⟨h, hu⟩ this
end
end MIPRE.TM.CookLevin

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.FreeFacts
open Turing SAT MultiInputTM
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S G : ℕ}
variable (s₀ s₁ : Symbol)
variable {s₀ s₁}
omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
theorem _root_.solution {a : TabVar i w Symbol State S G → Bool} {j : Fin i}
    (F : FreeFacts s₀ s₁ a j) (p : Pos S) (v : CellVal Symbol) :
    a (.cell 0 (.inl j) p v) = decide (v = inputCellVal (freeString a j s₀ s₁) p) := by
  by_cases hb : p.IsBdry
  · rw [F.bdry p v hb, (inputCellVal_bdry_iff _ _).mpr hb]
  by_cases h2 : (p : ℕ) = 2
  · rw [show p = ⟨2, Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 7 (2 * S))⟩ from Fin.ext h2,
      F.two v, inputCellVal_two]
  have h3 : 3 ≤ (p : ℕ) := by rw [not_isBdry_iff] at hb; omega
  obtain ⟨k, hk3, rfl⟩ : ∃ k, ∃ hk3 : k + 3 < numCells S, p = ⟨k + 3, hk3⟩ :=
    ⟨(p : ℕ) - 3, by have := p.isLt; omega, Fin.ext (by dsimp only; omega)⟩
  have hk5 : k + 5 < numCells S := by
    rw [not_isBdry_iff] at hb; dsimp only at hb; omega
  have hlen := length_freeString a j s₀ s₁
  rw [inputCellVal_eq _ _ hb, if_pos (by omega)]
  simp only [Nat.add_sub_cancel]
  by_cases hkn : k < freeLen a j
  · have hmin := freeLen_min a j hkn
    have hblank : a (.cell 0 (.inl j) ⟨k + 3, hk3⟩ .blank) = false := by
      have : blankBit a j k = a (.cell 0 (.inl j) ⟨k + 3, hk3⟩ .blank) := dif_pos hk3
      rw [← this]
      cases h : blankBit a j k
      · rfl
      · exact absurd (Or.inl h) hmin
    have hsym : symBit a j s₀ k = a (.cell 0 (.inl j) ⟨k + 3, hk3⟩ (.sym s₀)) := dif_pos hk3
    rw [List.getElem?_eq_getElem (by rw [hlen]; exact hkn)]
    simp only [freeString, List.getElem_ofFn]
    rw [hsym]
    rcases F.some _ hb with h0 | h1 | hbl
    · rw [h0, if_pos rfl]; exact F.onehot _ hb _ h0 v
    · cases h0 : a (.cell 0 (.inl j) ⟨k + 3, hk3⟩ (.sym s₀))
      · rw [if_neg Bool.false_ne_true]; exact F.onehot _ hb _ h1 v
      · rw [if_pos rfl]; exact F.onehot _ hb _ h0 v
    · rw [hblank] at hbl; exact absurd hbl Bool.false_ne_true
  · have hnk : freeLen a j ≤ k := Nat.le_of_not_lt hkn
    rcases freeLen_spec a j with hbn | hbn
    swap; · omega
    have hn3 : freeLen a j + 3 < numCells S := by omega
    have hcell : a (.cell 0 (.inl j) ⟨freeLen a j + 3, hn3⟩ .blank) = true := by
      have : blankBit a j (freeLen a j) =
          a (.cell 0 (.inl j) ⟨freeLen a j + 3, hn3⟩ .blank) := dif_pos hn3
      rw [← this]; exact hbn
    have hblank : a (.cell 0 (.inl j) ⟨k + 3, hk3⟩ .blank) = true := by
      rcases Nat.eq_or_lt_of_le hnk with h | h
      · subst h; exact hcell
      · exact F.mono ⟨freeLen a j + 3, hn3⟩ ⟨k + 3, hk3⟩ (by dsimp only; omega) hb
          (Fin.lt_def.mpr (by dsimp only; omega)) hcell
    rw [List.getElem?_eq_none (by rw [hlen]; exact hnk)]
    exact F.onehot _ hb _ hblank v
end MIPRE.TM.CookLevin.FreeFacts
