-- Prove2me | solution 1 for KernelRamsey.no_avoid_44
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T18:35:49.383073+00:00
-- url     : https://prove2.me/submissions/54a49940-fede-4ca2-a5da-15f3e005f599

import Mathlib
import Definitions.Def_KernelRamsey_Ram
import Theorems.Thm_KernelRamsey_ram2_44
open KernelRamsey Finset

theorem solution : ∀ G : SimpleGraph (Fin 18), ¬ (G.CliqueFree 4 ∧ Gᶜ.CliqueFree 4) := by
  intro G ⟨h1, h2⟩
  rcases ram2_44 G (Finset.univ : Finset (Fin 18)) (by simp) with ⟨T, _, hT⟩ | ⟨I, _, hI⟩
  · exact h1 T hT
  · exact h2 I hI
