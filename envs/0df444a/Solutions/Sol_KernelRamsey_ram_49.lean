-- Prove2me | solution 1 for KernelRamsey.ram_49
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T17:36:05.521612+00:00
-- url     : https://prove2.me/submissions/58f67dd2-2286-405e-a9a8-d04b7554ac98

import Mathlib
import Definitions.Def_KernelRamsey_Ram
import Theorems.Thm_KernelRamsey_nbhd_lt
import Theorems.Thm_KernelRamsey_card_split
import Theorems.Thm_KernelRamsey_nonnbr_false
import Theorems.Thm_KernelRamsey_ram_33
import Theorems.Thm_KernelRamsey_even_card_adjacent_pairs
open KernelRamsey Finset

theorem solution : Ram 4 9 := by
  classical
  intro V G A hA
  by_contra hno
  push Not at hno
  obtain ⟨hnoT, hnoI⟩ := hno
  obtain ⟨B, hBA, hB⟩ := Finset.exists_subset_card_eq hA
  have hnoT' : ∀ T ⊆ B, ¬ G.IsNClique 3 T := fun T hT => hnoT T (hT.trans hBA)
  have hnoI' : ∀ I ⊆ B, ¬ Gᶜ.IsNClique 4 I := fun I hI => hnoI I (hI.trans hBA)
  have hdeg : ∀ v ∈ B, (B.filter (fun w => G.Adj v w)).card = 3 := by
    intro v hv
    have hlt := nbhd_lt G hnoT' hnoI' hv
    have hs := card_split G B hv
    by_contra hne
    exact nonnbr_false G (t := 4) (m := 6) ram_33 (by norm_num) hnoT' hnoI' hv (by omega)
  have hsum : ((B ×ˢ B).filter (fun p => G.Adj p.1 p.2)).card = 27 := by
    have : ((B ×ˢ B).filter (fun p => G.Adj p.1 p.2)).card =
        ∑ v ∈ B, (B.filter (fun w => G.Adj v w)).card := by
      simp only [Finset.card_filter, Finset.sum_product]
    rw [this, Finset.sum_congr rfl hdeg]
    simp [hB]
  have := even_card_adjacent_pairs G B
  rw [hsum] at this
  exact absurd this (by decide)
