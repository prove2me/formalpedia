-- Prove2me | solution 1 for MIPRE.TM.CookLevin.headCell_step_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:48:32.685005+00:00
-- url     : https://prove2.me/submissions/8ef12478-64a2-494e-a1e6-6b76b3a2254c

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Semantics.lean (solution of MIPRE.TM.CookLevin.headCell_step_le);
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
theorem step_inputPos (c : Cfg i w Symbol State input) {q : State} (hst : c.state = some q)
    (j : Fin i) : (M.step c).inputPos j =
      moveInputPos (c.inputPos j) ((M.tr q c.inputSymbols c.workTapeSymbols).inputMoves j) := by
  unfold step; rw [hst]
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
theorem step_workTapePos (c : Cfg i w Symbol State input) {q : State} (hst : c.state = some q)
    (j : Fin w) : (M.step c).workTapePos j =
      c.workTapePos j + ((M.tr q c.inputSymbols c.workTapeSymbols).workActions j).2 := by
  unfold step; rw [hst]
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos moveInputPos_zero)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
variable (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem moveInputPos_sub_le {n : ℕ} (p : Fin (n + 2)) (m : SignType) :
    -1 ≤ ((moveInputPos p m : ℕ) : ℤ) - (p : ℤ) ∧ ((moveInputPos p m : ℕ) : ℤ) - (p : ℤ) ≤ 1 := by
  have hp := p.isLt
  unfold moveInputPos
  dsimp only
  split_ifs with h <;> cases m <;> simp only [SignType.cast] at h ⊢ <;> omega
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
omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem _root_.solution (c : Cfg i w Symbol State input) (d : Tape i w) :
    -1 ≤ headCell (S := S) (M.step c) d - headCell (S := S) c d ∧
      headCell (S := S) (M.step c) d - headCell (S := S) c d ≤ 1 := by
  cases hst : c.state with
  | none => rw [step_of_halt hst]; omega
  | some q =>
    cases d with
    | inl j =>
      simp only [headCell, step_inputPos M c hst]
      have := moveInputPos_sub_le (c.inputPos j)
        ((M.tr q c.inputSymbols c.workTapeSymbols).inputMoves j)
      omega
    | inr j =>
      simp only [headCell, step_workTapePos M c hst]
      cases ((M.tr q c.inputSymbols c.workTapeSymbols).workActions j).2 <;>
        simp [SignType.cast]
end MIPRE.TM.CookLevin
