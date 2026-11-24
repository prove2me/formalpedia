-- Prove2me | solution 1 for KernelRamsey.no_avoid_34
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T17:49:03.627549+00:00
-- url     : https://prove2.me/submissions/f0aeb0b2-0669-4290-ac72-c0b2d195d300

import Mathlib
import Definitions.Def_KernelRamsey_Ram
import Theorems.Thm_KernelRamsey_ram_49
open KernelRamsey Finset

theorem solution : ∀ G : SimpleGraph (Fin 9), ¬ (G.CliqueFree 3 ∧ Gᶜ.CliqueFree 4) := by
  intro G ⟨h1, h2⟩
  rcases ram_49 G (Finset.univ : Finset (Fin 9)) (by simp) with ⟨T, _, hT⟩ | ⟨I, _, hI⟩
  · exact h1 T hT
  · exact h2 I hI
