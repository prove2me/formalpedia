-- Prove2me | solution 1 for Groundwork.Grid.sum_patOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:09:50.103118+00:00
-- url     : https://prove2.me/submissions/8f05c3cb-c396-465e-8a87-340653435107

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_Digits
import Theorems.Thm_Groundwork_Grid_ixOf_bijOn
import Theorems.Thm_Groundwork_Prog_sum_digits
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_tuples
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit



set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (digit nRect)
namespace Groundwork.Grid
theorem _root_.solution (g n : ℕ) (F : (Rect (Fin g) (Fin g) → ℕ) → ℤ) :
    ∑ y ∈ range ((n + 1) ^ nRect g), F (patOf g n y) = ∑ ι ∈ Pat (Fin g) (Fin g) n, F ι := by
  have hlt : ∀ ω ∈ Ω (Fin g) (Fin g), ixOf g ω < nRect g := fun ω hω =>
    Finset.mem_range.1 (Finset.mem_coe.1 ((ixOf_bijOn g).mapsTo (Finset.mem_coe.2 hω)))
  -- a function of the numbers of the rectangles, read as a function of the rectangles
  set E : (Fin (nRect g) → ℕ) → Rect (Fin g) (Fin g) → ℕ :=
    fun φ ω => if h : ω ∈ Ω (Fin g) (Fin g) then φ ⟨ixOf g ω, hlt ω h⟩ else 0 with hE
  have h1 : ∀ y, patOf g n y = E fun q => digit n y q := by
    intro y
    funext ω
    simp only [patOf, hE]
    split_ifs <;> rfl
  have hs : ∀ q : Fin (nRect g), ∃ ω ∈ Ω (Fin g) (Fin g), ixOf g ω = q := fun q => by
    obtain ⟨ω, hω, hq⟩ := (ixOf_bijOn g).surjOn (Finset.mem_coe.2 (Finset.mem_range.2 q.2))
    exact ⟨ω, Finset.mem_coe.1 hω, hq⟩
  choose inv hinv1 hinv2 using hs
  simp only [h1]
  rw [Prog.sum_digits n (nRect g) fun φ => F (E φ)]
  refine Finset.sum_nbij E ?_ ?_ ?_ fun _ _ => rfl
  · intro φ hφ
    rw [Pat, mem_tuples]
    refine fun ω => ⟨fun h => ?_, fun h => ?_⟩
    · simp only [hE, dif_pos h]
      exact Fintype.mem_piFinset.1 hφ _
    · simp only [hE, dif_neg h]
  · intro φ _ φ' _ heq
    funext q
    have h2 := congrFun heq (inv q)
    simp only [hE, dif_pos (hinv1 q)] at h2
    have hq : (⟨ixOf g (inv q), hlt _ (hinv1 q)⟩ : Fin (nRect g)) = q := Fin.ext (hinv2 q)
    rwa [hq] at h2
  · intro ι hι
    have hι' := (mem_tuples _ _ _ _).1 (Finset.mem_coe.1 hι)
    refine ⟨fun q => ι (inv q), Finset.mem_coe.2 (Fintype.mem_piFinset.2 fun q => (hι' (inv q)).1 (hinv1 q)), ?_⟩
    funext ω
    by_cases h : ω ∈ Ω (Fin g) (Fin g)
    · simp only [hE, dif_pos h]
      exact congrArg ι ((ixOf_bijOn g).injOn (Finset.mem_coe.2 (hinv1 _)) (Finset.mem_coe.2 h) (hinv2 _))
    · simp only [hE, dif_neg h]
      exact ((hι' ω).2 h).symm
end Groundwork.Grid
