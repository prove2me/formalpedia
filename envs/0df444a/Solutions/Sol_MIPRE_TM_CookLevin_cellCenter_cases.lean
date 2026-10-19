-- Prove2me | solution 1 for MIPRE.TM.CookLevin.cellCenter_cases
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:29:35.99526+00:00
-- url     : https://prove2.me/submissions/01840cc5-890c-47ff-90c4-12d7034c811a

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Sound.lean (solution of MIPRE.TM.CookLevin.cellCenter_cases);
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
omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
/-- The head of tape `d` is in the window at offset `δ` iff its cell is that cell. -/
theorem headPre_localCfgOf (c : Cfg i w Symbol State input) (js : Tape i w → Center S)
    (d : Tape i w) (δ : Fin 5) :
    (localCfgOf M acc c js).headPre d δ = true ↔
      headCell (S := S) c d = ((cellIdx (js d) δ : Pos S) : ℕ) := by
  simp [localCfgOf]
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos moveInputPos_zero)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
variable (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
theorem headAt_localCfgOf (c : Cfg i w Symbol State input) (js : Tape i w → Center S)
    (d : Tape i w) (δ : Fin 5) (h : headCell (S := S) c d = ((cellIdx (js d) δ : Pos S) : ℕ)) :
    (localCfgOf M acc c js).HeadAt d δ := by
  intro δ'
  simp only [localCfgOf, cellIdx_val, h]
  by_cases hδ : δ' = δ
  · subst hδ; simp
  · have : (js d : ℕ) + (δ : ℕ) ≠ (js d : ℕ) + (δ' : ℕ) := by
      intro e; exact hδ (Fin.ext (by omega)).symm
    simp [hδ]
    omega
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S G : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
theorem headAt_headCenter (c : Cfg i w Symbol State input) (hin : HeadsIn c S)
    (js : Tape i w → Center S) (d : Tape i w) (hd : js d = headCenter c hin d) :
    (localCfgOf M acc c js).HeadAt d 2 := by
  apply headAt_localCfgOf
  rw [hd]
  simp only [cellIdx_val, headCenter, Fin.val_two]
  have := headCell_sub_two_toNat c hin d
  push_cast
  omega
end
end MIPRE.TM.CookLevin

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin
open Turing SAT MultiInputTM
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S G : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
theorem _root_.solution (c : Cfg i w Symbol State input) (hin : HeadsIn c S) (d : Tape i w)
    (p : Pos S) (hnb : ¬ p.IsBdry) :
    (∀ d', ∃ δ : Fin 5, 1 ≤ (δ : ℕ) ∧ (δ : ℕ) ≤ 3 ∧
      (localCfgOf M acc c (cellCenter c hin d p hnb)).HeadAt d' δ) ∨
    (localCfgOf M acc c (cellCenter c hin d p hnb)).HeadFar d := by
  by_cases hnear : ∃ δ : Fin 5, 1 ≤ (δ : ℕ) ∧ (δ : ℕ) ≤ 3 ∧
      headCell (S := S) c d = ((cellIdx (cellCenter c hin d p hnb d) δ : Pos S) : ℕ)
  · left
    intro d'
    by_cases hd : d' = d
    · subst hd
      obtain ⟨δ, h1, h3, hδ⟩ := hnear
      exact ⟨δ, h1, h3, headAt_localCfgOf M acc c _ d' δ hδ⟩
    · exact ⟨2, by simp, by simp, headAt_headCenter M acc c hin _ d'
        (by simp only [cellCenter, if_neg hd])⟩
  · right
    have h : ∀ δ : Fin 5, 1 ≤ (δ : ℕ) → (δ : ℕ) ≤ 3 →
        (localCfgOf M acc c (cellCenter c hin d p hnb)).headPre d δ = false := by
      intro δ h1 h3
      cases h : (localCfgOf M acc c (cellCenter c hin d p hnb)).headPre d δ
      · rfl
      · exact absurd ⟨δ, h1, h3, (headPre_localCfgOf M acc c _ d δ).mp h⟩ hnear
    exact ⟨h 1 (by simp) (by simp), h 2 (by simp) (by simp), h 3 (by simp) (by simp)⟩
end MIPRE.TM.CookLevin
