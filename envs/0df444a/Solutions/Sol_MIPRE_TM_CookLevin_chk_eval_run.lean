-- Prove2me | solution 1 for MIPRE.TM.CookLevin.chk_eval_run
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:51:17.973498+00:00
-- url     : https://prove2.me/submissions/3d868e4f-67a5-4f29-be3d-499644370a61

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Correct.lean (solution of MIPRE.TM.CookLevin.chk_eval_run);
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
import Theorems.Thm_MIPRE_TM_CookLevin_far_localCfgOf
import Theorems.Thm_MIPRE_TM_CookLevin_fullStep_localCfgOf
import Theorems.Thm_MIPRE_TM_CookLevin_inputPos_cfgAt_le
import Theorems.Thm_MIPRE_TM_CookLevin_workTapePos_cfgAt_bounds

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
omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem cfgAt_succ (t : ℕ) : cfgAt M (input := input) (t + 1) = M.step (cfgAt M t) :=
  configs_succ_eq_step'
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos moveInputPos_zero)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
variable (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [Fintype State] in
/-- The encoding of the local configuration of the run at `(t, js)` is the run's assignment
on the window's variables. -/
theorem encode_localCfgOf (G : ℕ) (t : Fin S) (js : Tape i w → Center S)
    (v : WinVar i w Symbol State) :
    (localCfgOf M acc (cfgAt M (input := input) t) js).encode v =
      baseAssign M acc (input := input) G (winVarOf (G := G) t js v) := by
  have hs : cfgAt M (input := input) ((t : ℕ) + 1) = M.step (cfgAt M t) := cfgAt_succ M t
  cases v <;> simp [LocalCfg.encode, localCfgOf, winVarOf, baseAssign, hs, Fin.val_castSucc,
    Fin.val_succ]
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
omit [Fintype Symbol] [Fintype State] [DecidableEq State] [DecidableEq Symbol] in
/-- At every time `t ≤ S`, every head of the run is on an interior cell. -/
theorem headsIn_cfgAt (t : ℕ) (ht : t ≤ S) : HeadsIn (cfgAt M (input := input) t) S where
  input_pos j := by have := inputPos_cfgAt_le M (input := input) t j; omega
  work_pos j := by have := workTapePos_cfgAt_bounds M (input := input) t j; omega
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
theorem outputString_zero (c : Cfg i w Symbol State input) : M.outputString c 0 = [] := by
  simp [outputString]
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
omit [Fintype Symbol] [Fintype State] in
theorem baseAssign_emitted_zero :
    baseAssign M acc (input := input) G (.emitted (0 : Fin (S + 1))) = false := by
  simp [baseAssign, outputString_zero]
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
/-- The bits of the window read from `f` are the values of `f` on the circuit's inputs. -/
theorem getD_winBits (f : TabVar i w Symbol State S G → Bool) (h0 : f (.emitted 0) = false)
    (t : Fin S) (js : Tape i w → Center S) (n : ℕ) :
    (winBits fun v => f (winVarOf (G := G) t js v)).getD n false = f (inpOf (G := G) t js n) := by
  unfold winBits inpOf
  by_cases h : n < winCard i w Symbol State
  · rw [dif_pos h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [dif_neg h, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using h)]
    simp [h0]
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
theorem _root_.solution (hchk : IsCheckCircuit M acc chk) (t : Fin S) (js : Tape i w → Center S) :
    chk.eval (fun n => baseAssign M acc (input := input) chk.gates.length
      (inpOf (G := chk.gates.length) t js n)) = true := by
  have := hchk (fun v => baseAssign M acc (input := input) chk.gates.length
    (winVarOf (G := chk.gates.length) t js v))
  have hfun : (fun n => (winBits fun v => baseAssign M acc (input := input) chk.gates.length
      (winVarOf (G := chk.gates.length) t js v)).getD n false) =
      fun n => baseAssign M acc (input := input) chk.gates.length
        (inpOf (G := chk.gates.length) t js n) :=
    funext (getD_winBits _ (baseAssign_emitted_zero M acc : baseAssign M acc (input := input)
      chk.gates.length (.emitted (0 : Fin (S + 1))) = false) t js)
  unfold Circuit.evalBits at this
  rw [hfun] at this
  refine this.mpr ?_
  exact ⟨localCfgOf M acc (cfgAt M (input := input) t) js, funext (encode_localCfgOf M acc _ t js),
    locallyConsistent_localCfgOf M acc _ js (headsIn_cfgAt M (input := input) t (by omega))⟩
end MIPRE.TM.CookLevin
