-- Prove2me | solution 1 for MIPRE.TM.CookLevin.far_localCfgOf
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:49:19.416631+00:00
-- url     : https://prove2.me/submissions/355201a4-db68-4511-bca0-fc4dcd1a70fb

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Semantics.lean (solution of MIPRE.TM.CookLevin.far_localCfgOf);
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
import Theorems.Thm_MIPRE_TM_CookLevin_headCell_step_le

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
theorem step_workTapes (c : Cfg i w Symbol State input) {q : State} (hst : c.state = some q)
    (j : Fin w) : (M.step c).workTapes j =
      match ((M.tr q c.inputSymbols c.workTapeSymbols).workActions j).1 with
      | none => c.workTapes j
      | some s => Function.update (c.workTapes j) (c.workTapePos j) s := by
  unfold step; rw [hst]; rfl
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
omit [Fintype Symbol] [Fintype State] [DecidableEq State] in
theorem _root_.solution (c : Cfg i w Symbol State input) (js : Tape i w → Center S) (d : Tape i w)
    (hfar : (localCfgOf M acc c js).HeadFar d) :
    (localCfgOf M acc c js).cellPost d = (localCfgOf M acc c js).cellPre d 2 ∧
      (localCfgOf M acc c js).headPost d = false := by
  obtain ⟨h1, h2, h3⟩ := hfar
  simp only [localCfgOf, decide_eq_false_iff_not, cellIdx_val, Fin.val_one, Fin.val_two,
    show ((3 : Fin 5) : ℕ) = 3 from rfl, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h1 h2 h3
  have hstep := headCell_step_le (S := S) M c d
  have hne : headCell (S := S) (M.step c) d ≠ ((center (js d) : Pos S) : ℕ) := by
    simp only [center_val, Nat.cast_add, Nat.cast_ofNat]; omega
  refine ⟨?_, by simpa [localCfgOf] using hne⟩
  simp only [localCfgOf, center]
  cases d with
  | inl j => rfl
  | inr j =>
    simp only [cellValAt]
    split_ifs with hb
    · rfl
    · congr 1
      cases hst : c.state with
      | none => rw [step_of_halt hst]
      | some q =>
        rw [step_workTapes M c hst]
        cases ((M.tr q c.inputSymbols c.workTapeSymbols).workActions j).1 with
        | none => rfl
        | some s =>
          simp only
          rw [Function.update_of_ne]
          simp only [headCell] at h2
          simp only [cellIdx_val, Fin.val_two, Nat.cast_add, Nat.cast_ofNat]
          omega
end MIPRE.TM.CookLevin
