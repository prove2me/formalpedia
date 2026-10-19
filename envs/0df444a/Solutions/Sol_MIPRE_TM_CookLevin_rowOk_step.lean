-- Prove2me | solution 1 for MIPRE.TM.CookLevin.rowOk_step
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:31:58.960813+00:00
-- url     : https://prove2.me/submissions/7287e285-5543-46fd-998c-c4fd570122fa

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Sound.lean (solution of MIPRE.TM.CookLevin.rowOk_step);
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
import Theorems.Thm_MIPRE_TM_CookLevin_HeadsIn_headCell_bounds
import Theorems.Thm_MIPRE_TM_CookLevin_cellCenter_cases
import Theorems.Thm_MIPRE_TM_CookLevin_far_localCfgOf
import Theorems.Thm_MIPRE_TM_CookLevin_fullStep_localCfgOf
import Theorems.Thm_MIPRE_TM_CookLevin_not_isBdry_iff
import Theorems.Thm_MIPRE_TM_CookLevin_post_of_pre
import Theorems.Thm_MIPRE_TM_CookLevin_window_of_sat

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos moveInputPos_zero)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
theorem cellIdx_injective (c : Center S) : Function.Injective (cellIdx c) := by
  intro δ δ' h
  have := congrArg (fun p : Pos S => (p : ℕ)) h
  simp only [cellIdx_val] at this
  exact Fin.ext (by omega)
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
open MultiTapeTM (moveInputPos moveInputPos_zero)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
variable (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
/-- No two heads of a tape in a window of a run. -/
theorem not_twoHeads_localCfgOf (c : Cfg i w Symbol State input) (js : Tape i w → Center S)
    (d : Tape i w) : ¬ (localCfgOf M acc c js).TwoHeads d := by
  rintro ⟨δ, δ', hne, h, h'⟩
  rw [headPre_localCfgOf] at h h'
  exact hne (cellIdx_injective (js d) (Fin.ext (by simp only [cellIdx_val] at h h' ⊢; omega)))
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
open MultiTapeTM (moveInputPos moveInputPos_zero)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
variable (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
/-- **The windows of a run are locally consistent.** -/
theorem locallyConsistent_localCfgOf (c : Cfg i w Symbol State input) (js : Tape i w → Center S)
    (hin : HeadsIn c S) : LocallyConsistent M acc (localCfgOf M acc c js) := by
  classical
  refine Or.inr ⟨fun d hfar => far_localCfgOf M acc c js d hfar, ?_⟩
  by_cases hall : ∀ d, ∃ δ : Fin 5, 1 ≤ (δ : ℕ) ∧ (δ : ℕ) ≤ 3 ∧ (localCfgOf M acc c js).HeadAt d δ
  · choose δ hδ using hall
    exact Or.inl ⟨δ, hδ, fullStep_localCfgOf M acc c js hin δ hδ⟩
  · exact Or.inr hall
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
theorem cellValAt_bdry (c : Cfg i w Symbol State input) (d : Tape i w) (p : Pos S) (hb : p.IsBdry) :
    cellValAt (S := S) c d p = .bdry := by
  cases d with
  | inl j => exact (inputCellVal_bdry_iff _ _).mpr hb
  | inr j => simp [cellValAt, hb]
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

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S G : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
theorem center_cellCenter (c : Cfg i w Symbol State input) (hin : HeadsIn c S) (d : Tape i w)
    (p : Pos S) (hnb : ¬ p.IsBdry) : center (cellCenter c hin d p hnb d) = p := by
  apply Fin.ext
  simp only [center_val, cellCenter, if_true]
  rw [not_isBdry_iff] at hnb
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
/-- Every head is in its window when the windows are centered at the heads. -/
theorem allIn_headCenter (c : Cfg i w Symbol State input) (hin : HeadsIn c S) :
    ∀ d, ∃ δ : Fin 5, 1 ≤ (δ : ℕ) ∧ (δ : ℕ) ≤ 3 ∧
      (localCfgOf M acc c (headCenter c hin)).HeadAt d δ :=
  fun d => ⟨2, by simp, by simp, headAt_headCenter M acc c hin _ d rfl⟩
end
end MIPRE.TM.CookLevin

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin
open Turing SAT MultiInputTM
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S G : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [Fintype State] in
theorem _root_.solution (a : TabVar i w Symbol State S G → Bool) (t : Fin S)
    (c : Cfg i w Symbol State input) (hrow : RowOk a t.castSucc c) (hin : HeadsIn c S)
    (hin' : HeadsIn (M.step c) S)
    (hwin : ∀ js, checkPred M acc (fun v => a (winVarOf (G := G) t js v)))
    (hbdry : ∀ d (p : Pos S) v, p.IsBdry → a (.cell t.succ d p v) = decide (v = .bdry))
    (hbdryh : ∀ d (p : Pos S), p.IsBdry → a (.head t.succ d p) = false) :
    RowOk a t.succ (M.step c) ∧ a (.emitOne t) = decide (M.outputSymbol c = some acc) ∧
      a (.emitBad t) = decide (M.outputSymbol c ≠ none ∧ M.outputSymbol c ≠ some acc) := by
  have key : ∀ js, ∃ L : LocalCfg i w Symbol State,
      (∀ v, L.encode v = a (winVarOf (G := G) t js v)) ∧
      (∀ d, (localCfgOf M acc c js).HeadFar d →
        L.cellPost d = (localCfgOf M acc c js).cellPost d ∧
        L.headPost d = (localCfgOf M acc c js).headPost d) ∧
      ((∀ d, ∃ δ : Fin 5, 1 ≤ (δ : ℕ) ∧ (δ : ℕ) ≤ 3 ∧ (localCfgOf M acc c js).HeadAt d δ) →
        L.cellPost = (localCfgOf M acc c js).cellPost ∧
        L.headPost = (localCfgOf M acc c js).headPost ∧
        L.statePost = (localCfgOf M acc c js).statePost ∧
        L.emitOne = (localCfgOf M acc c js).emitOne ∧
        L.emitBad = (localCfgOf M acc c js).emitBad) := by
    intro js
    obtain ⟨L, hLc, he, hc, hh, hs⟩ := window_of_sat M acc a t c hrow js (hwin js)
    exact ⟨L, he, post_of_pre M acc hLc (locallyConsistent_localCfgOf M acc c js hin)
      (not_twoHeads_localCfgOf M acc c js) hc hh hs⟩
  obtain ⟨L₀, he₀, -, hfull₀⟩ := key (headCenter c hin)
  obtain ⟨-, -, hs₀, ho₀, hb₀⟩ := hfull₀ (allIn_headCenter M acc c hin)
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro d p v
    by_cases hb : p.IsBdry
    · rw [hbdry d p v hb, cellValAt_bdry _ _ _ hb]
      exact decide_eq_decide.mpr eq_comm
    · obtain ⟨L, he, hfar, hfull⟩ := key (cellCenter c hin d p hb)
      have hcen := center_cellCenter c hin d p hb
      have hpost : L.cellPost d = (localCfgOf M acc c (cellCenter c hin d p hb)).cellPost d := by
        rcases cellCenter_cases M acc c hin d p hb with hall | hfar'
        · exact congrFun (hfull hall).1 d
        · exact (hfar d hfar').1
      have := he (.cellPost d v)
      simp only [LocalCfg.encode, winVarOf, hcen] at this
      rw [← this, hpost]
      simp only [localCfgOf, hcen]
  · intro d p
    by_cases hb : p.IsBdry
    · rw [hbdryh d p hb]
      apply (decide_eq_false _).symm
      intro h
      have hbd := hin'.headCell_bounds d
      have hnc : numCells S = 2 * S + 7 := rfl
      unfold Pos.IsBdry at hb
      omega
    · obtain ⟨L, he, hfar, hfull⟩ := key (cellCenter c hin d p hb)
      have hcen := center_cellCenter c hin d p hb
      have hpost : L.headPost d = (localCfgOf M acc c (cellCenter c hin d p hb)).headPost d := by
        rcases cellCenter_cases M acc c hin d p hb with hall | hfar'
        · exact congrFun (hfull hall).2.1 d
        · exact (hfar d hfar').2
      have := he (.headPost d)
      simp only [LocalCfg.encode, winVarOf, hcen] at this
      rw [← this, hpost]
      simp only [localCfgOf, hcen]
  · intro q
    have := he₀ (.statePost q)
    simp only [LocalCfg.encode, winVarOf] at this
    rw [← this, hs₀]
    rfl
  · have := he₀ .emitOne
    simp only [LocalCfg.encode, winVarOf] at this
    rw [← this, ho₀]
    rfl
  · have := he₀ .emitBad
    simp only [LocalCfg.encode, winVarOf] at this
    rw [← this, hb₀]
    rfl
end MIPRE.TM.CookLevin
