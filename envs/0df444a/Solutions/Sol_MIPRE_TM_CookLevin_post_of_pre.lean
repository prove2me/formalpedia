-- Prove2me | solution 1 for MIPRE.TM.CookLevin.post_of_pre
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:29:03.758778+00:00
-- url     : https://prove2.me/submissions/bd5dddc3-e92a-43a4-9e38-0f6b00387e06

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Sound.lean (solution of MIPRE.TM.CookLevin.post_of_pre);
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
import Theorems.Thm_MIPRE_TM_CookLevin_fullStep_post_eq

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
variable {i w : ℕ} {Symbol State : Type*} [DecidableEq Symbol] [DecidableEq State]
  (M : MultiInputTM i w Symbol State) (acc : Symbol)
omit [DecidableEq Symbol] [DecidableEq State] in
theorem LocalCfg.HeadAt.unique {L : LocalCfg i w Symbol State} {d : Tape i w} {δ δ' : Fin 5}
    (h : L.HeadAt d δ) (h' : L.HeadAt d δ') : δ = δ' := by
  have := (h' δ).symm.trans (h δ)
  simpa using this
end
end MIPRE.TM.CookLevin

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin
open Turing SAT MultiInputTM
variable {i w : ℕ} {Symbol State : Type*} [DecidableEq Symbol] [DecidableEq State]
  (M : MultiInputTM i w Symbol State) (acc : Symbol)
omit [DecidableEq State] in
theorem _root_.solution {L L' : LocalCfg i w Symbol State} (hL : LocallyConsistent M acc L)
    (hL' : LocallyConsistent M acc L') (hno : ∀ d, ¬ L'.TwoHeads d)
    (hc : L.cellPre = L'.cellPre) (hh : L.headPre = L'.headPre) (hs : L.statePre = L'.statePre) :
    (∀ d, L'.HeadFar d → L.cellPost d = L'.cellPost d ∧ L.headPost d = L'.headPost d) ∧
    ((∀ d, ∃ δ : Fin 5, 1 ≤ (δ : ℕ) ∧ (δ : ℕ) ≤ 3 ∧ L'.HeadAt d δ) →
      L.cellPost = L'.cellPost ∧ L.headPost = L'.headPost ∧ L.statePost = L'.statePost ∧
        L.emitOne = L'.emitOne ∧ L.emitBad = L'.emitBad) := by
  have hno' : ∀ d, ¬ L.TwoHeads d := fun d h =>
    hno d (by unfold LocalCfg.TwoHeads at h ⊢; rwa [hh] at h)
  have hat : ∀ d δ, L.HeadAt d δ ↔ L'.HeadAt d δ := fun d δ => by
    unfold LocalCfg.HeadAt; rw [hh]
  have hfarI : ∀ d, L.HeadFar d ↔ L'.HeadFar d := fun d => by
    unfold LocalCfg.HeadFar; rw [hh]
  rcases hL with ⟨d, h⟩ | ⟨hfar, hfull⟩
  · exact absurd h (hno' d)
  rcases hL' with ⟨d, h⟩ | ⟨hfar', hfull'⟩
  · exact absurd h (hno d)
  refine ⟨fun d hd => ?_, fun hall => ?_⟩
  · obtain ⟨c1, h1⟩ := hfar d ((hfarI d).mpr hd)
    obtain ⟨c1', h1'⟩ := hfar' d hd
    exact ⟨by rw [c1, c1', hc], by rw [h1, h1']⟩
  · have hall' : ∀ d, ∃ δ : Fin 5, 1 ≤ (δ : ℕ) ∧ (δ : ℕ) ≤ 3 ∧ L.HeadAt d δ := fun d =>
      let ⟨δ, h1, h2, h3⟩ := hall d; ⟨δ, h1, h2, (hat d δ).mpr h3⟩
    rcases hfull' with ⟨δ', hδ', hF'⟩ | hn
    swap; · exact absurd hall hn
    rcases hfull with ⟨δ, hδ, hF⟩ | hn
    swap; · exact absurd hall' hn
    have hδδ : δ = δ' := funext fun d =>
      LocalCfg.HeadAt.unique (hδ d).2.2 ((hat d (δ' d)).mpr (hδ' d).2.2)
    subst hδδ
    exact fullStep_post_eq M acc δ hF hF' hc hh hs
end MIPRE.TM.CookLevin
