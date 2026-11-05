-- Prove2me | solution 2 for GeneralPieces.Lex.lexNum_injOn
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:30:29.737996+00:00
-- url     : https://prove2.me/submissions/d2963606-e2c7-425a-b13f-bfec784eabd9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_Bridge
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Lex
import Definitions.Def_GeneralPieces_Ring_Lex
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Lex
open AppHalfPieces Finset

theorem solution (h : ℕ) : Set.InjOn (lexNum h) (ptns h) := by
  classical
  intro μ hμ ν hν hnum
  have aux : ∀ {μ ν : Ptn}, μ ∈ ptns h → ν ∈ ptns h →
      lexNum h μ = lexNum h ν → desc μ < desc ν → False := by
    intro μ ν hμ _ hnum hlt
    have hsub : {ρ ∈ ptns h | desc ρ < desc μ} ⊆ {ρ ∈ ptns h | desc ρ < desc ν} := by
      intro ρ hρ
      simp only [Finset.mem_filter] at hρ ⊢
      exact ⟨hρ.1, hρ.2.trans hlt⟩
    have heq : {ρ ∈ ptns h | desc ρ < desc μ} = {ρ ∈ ptns h | desc ρ < desc ν} :=
      Finset.eq_of_subset_of_card_le hsub (by simpa only [lexNum] using hnum.ge)
    have hmem : μ ∈ {ρ ∈ ptns h | desc ρ < desc ν} := by
      simp only [Finset.mem_filter]
      exact ⟨hμ, hlt⟩
    rw [← heq] at hmem
    exact (lt_irrefl (desc μ)) (Finset.mem_filter.mp hmem).2
  have hdesc : desc μ = desc ν := by
    rcases lt_trichotomy (desc μ) (desc ν) with hlt | heq | hgt
    · exact (aux hμ hν hnum hlt).elim
    · exact heq
    · exact (aux hν hμ hnum.symm hgt).elim
  have hmap : μ.map (fun k : ℕ+ => (k : ℕ)) = ν.map (fun k : ℕ+ => (k : ℕ)) := by
    simpa only [desc, Multiset.sort_eq] using
      congrArg (fun l : List ℕ => (l : Multiset ℕ)) hdesc
  exact Multiset.map_injective Subtype.val_injective hmap
