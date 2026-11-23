-- Prove2me | solution 1 for IterStar_seg_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:35:03.41933+00:00
-- url     : https://prove2.me/submissions/3a9ecf34-7cb1-486e-aac0-6076afdf173c

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic
import Theorems.Thm_IterFin_seg_exists

set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}
theorem _root_.solution {L : Set (List A)} {al : List A} (h : al ∈ L∗) :
    ∃ n, ∃ φ : Stream' ℕ, StrictMonoOn φ {k | k < n + 1} ∧ φ 0 = 0 ∧ φ n = al.length ∧
      ∀ k < n, al.extract (φ k) (φ (k + 1)) ∈ L := by
  change ∃ n, ∃ φ : ℕ → ℕ, StrictMonoOn φ {k | k < n + 1} ∧ φ 0 = 0 ∧ φ n = al.length ∧
    ∀ k < n, al.extract (φ k) (φ (k + 1)) ∈ L
  change al ∈ IterStar L at h
  simp only [IterStar, Set.mem_iUnion] at h
  obtain ⟨m, h_m⟩ := h
  obtain ⟨n, h_n, h_ex⟩ := IterFin_seg_exists h_m
  exact ⟨n, h_ex⟩
