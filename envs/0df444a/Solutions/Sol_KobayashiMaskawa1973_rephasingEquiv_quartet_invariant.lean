-- Prove2me | solution 1 for KobayashiMaskawa1973.rephasingEquiv_quartet_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T18:30:04.761713+00:00
-- url     : https://prove2.me/submissions/4274c719-2010-420c-a01f-de5ae7dcbe92

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs
import Theorems.Thm_KobayashiMaskawa1973_rephasingEquiv_entry
import Theorems.Thm_KobayashiMaskawa1973_quartet_phase_cancellation

open Matrix
open KobayashiMaskawa1973

theorem solution (U V : Matrix (Fin 3) (Fin 3) ℂ) (h : RephasingEquiv U V) :
    V 0 0 * V 1 1 * star (V 0 1) * star (V 1 0) = U 0 0 * U 1 1 * star (U 0 1) * star (U 1 0) := by
  obtain ⟨a, b, hab⟩ := h
  rw [rephasingEquiv_entry U V a b hab 0 0]
  rw [rephasingEquiv_entry U V a b hab 1 1]
  rw [rephasingEquiv_entry U V a b hab 0 1]
  rw [rephasingEquiv_entry U V a b hab 1 0]
  exact quartet_phase_cancellation (U 0 0) (U 1 1) (U 0 1) (U 1 0) (a 0) (a 1) (b 0) (b 1)
