-- Prove2me | solution 1 for MIPRE.TM.CookLevin.fullStep_post_eq
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:28:01.437699+00:00
-- url     : https://prove2.me/submissions/4cd46623-6d17-4b54-858a-81292cf408bd

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Sound.lean (solution of MIPRE.TM.CookLevin.fullStep_post_eq);
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin
open Turing SAT MultiInputTM
variable {i w : ℕ} {Symbol State : Type*} [DecidableEq Symbol] [DecidableEq State]
  (M : MultiInputTM i w Symbol State) (acc : Symbol)
omit [DecidableEq State] in
theorem _root_.solution {L L' : LocalCfg i w Symbol State} (δ : Tape i w → Fin 5)
    (hL : FullStep M acc L δ) (hL' : FullStep M acc L' δ)
    (hc : L.cellPre = L'.cellPre) (hh : L.headPre = L'.headPre) (hs : L.statePre = L'.statePre) :
    L.cellPost = L'.cellPost ∧ L.headPost = L'.headPost ∧ L.statePost = L'.statePost ∧
      L.emitOne = L'.emitOne ∧ L.emitBad = L'.emitBad := by
  obtain ⟨cp, hp, cpo, hpo, sp, spo, e1, e2⟩ := L
  obtain ⟨cp', hp', cpo', hpo', sp', spo', e1', e2'⟩ := L'
  simp only at hc hh hs
  subst hc hh hs
  unfold FullStep at hL hL'
  cases sp with
  | none =>
    dsimp only at hL hL'
    obtain ⟨c1, h1, s1, o1, b1⟩ := hL
    obtain ⟨c1', h1', s1', o1', b1'⟩ := hL'
    dsimp only
    refine ⟨funext fun d => ?_, funext fun d => ?_, ?_, ?_, ?_⟩
    · rw [c1, c1']
    · rw [h1, h1']
    · rw [s1, s1']
    · rw [o1, o1']
    · rw [b1, b1']
  | some q =>
    dsimp only at hL hL'
    obtain ⟨-, c1, c2, h1, h2, s1, o1, b1⟩ := hL
    obtain ⟨-, c1', c2', h1', h2', s1', o1', b1'⟩ := hL'
    dsimp only
    refine ⟨funext fun d => ?_, funext fun d => ?_, ?_, ?_, ?_⟩
    · cases d with
      | inl j => rw [c1, c1']
      | inr j => rw [c2, c2']
    · cases d with
      | inl j => rw [h1, h1']
      | inr j => rw [h2, h2']
    · rw [s1, s1']
    · rw [o1, o1']
    · rw [b1, b1']
end MIPRE.TM.CookLevin
