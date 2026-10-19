-- Prove2me | solution 1 for MIPRE.TM.CookLevin.outputSymbol_of_accepting
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:46:37.496556+00:00
-- url     : https://prove2.me/submissions/7647b799-086d-4ed4-94be-188ecd59e47e

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Correct.lean (solution of MIPRE.TM.CookLevin.outputSymbol_of_accepting);
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace Turing.MultiInputTM
section
open Relation
open MultiTapeTM (moveInputPos)
open Cfg
variable {i w : ℕ} {State Symbol : Type*}
variable {tm : MultiInputTM i w Symbol State}
variable {input : Fin i → List Symbol}
/-- The output produced in `t + 1` steps is the output produced in `t` steps followed by
the symbol (optionally) emitted at step `t`. -/
lemma outputString_succ
    (tm : MultiInputTM i w Symbol State)
    (cfg : Cfg i w Symbol State input) (t : ℕ) :
    tm.outputString cfg (t + 1) =
      tm.outputString cfg t ++ (tm.outputSymbol (tm.configs cfg t)).toList := by
  simp [outputString, List.range_succ, List.flatMap_append]
end
end Turing.MultiInputTM

namespace Turing.MultiInputTM
section
open Relation
open MultiTapeTM (moveInputPos)
open Cfg
variable {i w : ℕ} {State Symbol : Type*}
variable {tm : MultiInputTM i w Symbol State}
variable {input : Fin i → List Symbol}
lemma outputString_add_eq_append
    (tm : MultiInputTM i w Symbol State)
    (cfg : Cfg i w Symbol State input) (t₁ t₂ : ℕ) :
    tm.outputString cfg (t₁ + t₂) =
      tm.outputString cfg t₁ ++ tm.outputString (tm.configs cfg t₁) t₂ := by
  induction t₂ with
  | zero => simp [outputString]
  | succ t ih =>
    rw [show (t₁ + (t + 1)) = (t₁ + t) + 1 by omega]
    simp [outputString_succ, ih, configs, ← Function.iterate_add_apply, Nat.add_comm]
end
end Turing.MultiInputTM

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
/-- The output of `S` steps, split at step `t`. -/
theorem outputString_split (t : ℕ) (ht : t < S) :
    M.outputString (M.initCfg input) S =
      M.outputString (M.initCfg input) t ++ (M.outputSymbol (cfgAt M (input := input) t)).toList ++
        M.outputString (cfgAt M (input := input) (t + 1)) (S - (t + 1)) := by
  have h1 : S = (t + 1) + (S - (t + 1)) := by omega
  conv_lhs => rw [h1]
  rw [outputString_add_eq_append, outputString_succ]
  rfl
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
theorem singleton_eq_append₃ {α : Type*} {x : α} {A B C : List α} (h : [x] = A ++ B ++ C) :
    (B ≠ [] → A = [] ∧ B = [x] ∧ C = []) ∧ (A ≠ [] → B = []) := by
  have hl := congrArg List.length h
  simp only [List.length_singleton, List.length_append] at hl
  constructor
  · intro hB
    have hB' : 0 < B.length := List.length_pos_iff.mpr hB
    have hA : A = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hC : C = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hA hC
    exact ⟨rfl, by simpa using h.symm, rfl⟩
  · intro hA
    have := List.length_pos_iff.mpr hA
    exact List.eq_nil_of_length_eq_zero (by omega)
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
omit [Fintype Symbol] [DecidableEq Symbol] [Fintype State] [DecidableEq State] in
theorem _root_.solution (hacc : M.outputString (M.initCfg input) S = [acc]) (t : ℕ)
    (ht : t < S) (hne : M.outputSymbol (cfgAt M (input := input) t) ≠ none) :
    M.outputSymbol (cfgAt M (input := input) t) = some acc ∧
      M.outputString (M.initCfg input) t = [] := by
  have h := outputString_split M (input := input) t ht
  rw [hacc] at h
  have hB : (M.outputSymbol (cfgAt M (input := input) t)).toList ≠ [] := by
    cases hm : M.outputSymbol (cfgAt M (input := input) t)
    · exact absurd hm hne
    · simp
  obtain ⟨hA, hB', -⟩ := (singleton_eq_append₃ h).1 hB
  refine ⟨?_, hA⟩
  cases hm : M.outputSymbol (cfgAt M (input := input) t) with
  | none => exact absurd hm hne
  | some s => rw [hm] at hB'; simpa using hB'
end MIPRE.TM.CookLevin
