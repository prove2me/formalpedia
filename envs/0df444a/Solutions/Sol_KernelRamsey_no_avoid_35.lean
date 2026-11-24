-- Prove2me | solution 1 for KernelRamsey.no_avoid_35
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T18:02:25.673882+00:00
-- url     : https://prove2.me/submissions/1352cee6-64b9-489b-9b72-6f3d37679537

import Mathlib
import Definitions.Def_KernelRamsey_Ram
import Theorems.Thm_KernelRamsey_ram_35
open KernelRamsey Finset

theorem solution : ∀ G : SimpleGraph (Fin 14), ¬ (G.CliqueFree 3 ∧ Gᶜ.CliqueFree 5) := by
  intro G ⟨h1, h2⟩
  rcases ram_35 G (Finset.univ : Finset (Fin 14)) (by simp) with ⟨T, _, hT⟩ | ⟨I, _, hI⟩
  · exact h1 T hT
  · exact h2 I hI
