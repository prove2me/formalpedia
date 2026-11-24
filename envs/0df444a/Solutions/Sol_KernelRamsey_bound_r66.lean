-- Prove2me | solution 1 for KernelRamsey.bound_r66
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T18:20:18.450939+00:00
-- url     : https://prove2.me/submissions/09da68de-2a1c-45c9-b22d-75c69c2da126

import Mathlib
import Definitions.Def_KernelRamsey_Mask
import Definitions.Def_KernelRamsey_Witnesses
import Theorems.Thm_KernelRamsey_ramsey_avoidance
import Theorems.Thm_KernelRamsey_noClique_chain
import Theorems.Thm_KernelRamsey_bound_r66_g0
import Theorems.Thm_KernelRamsey_bound_r66_g1
import Theorems.Thm_KernelRamsey_bound_r66_g2
import Theorems.Thm_KernelRamsey_bound_r66_g3
import Theorems.Thm_KernelRamsey_bound_r66_g4
import Theorems.Thm_KernelRamsey_bound_r66_g5
import Theorems.Thm_KernelRamsey_bound_r66_g6
import Theorems.Thm_KernelRamsey_bound_r66_g7
import Theorems.Thm_KernelRamsey_bound_r66_g8
import Theorems.Thm_KernelRamsey_bound_r66_g9
import Theorems.Thm_KernelRamsey_bound_r66_c0
import Theorems.Thm_KernelRamsey_bound_r66_c1
import Theorems.Thm_KernelRamsey_bound_r66_c2
import Theorems.Thm_KernelRamsey_bound_r66_c3
import Theorems.Thm_KernelRamsey_bound_r66_c4
import Theorems.Thm_KernelRamsey_bound_r66_c5
import Theorems.Thm_KernelRamsey_bound_r66_c6
import Theorems.Thm_KernelRamsey_bound_r66_c7
import Theorems.Thm_KernelRamsey_bound_r66_c8
import Theorems.Thm_KernelRamsey_bound_r66_c9
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open KernelRamsey

theorem solution : ∃ G : SimpleGraph (Fin 101), G.CliqueFree 6 ∧ Gᶜ.CliqueFree 6 := by
  have hg : ∀ p : Nat, p < 101 → noClique (rows_r66) p 5 ((2 ^ p - 1) &&& row (rows_r66) p) = true := by
    intro p hp
    have hc : (p < 10 ∧ 0 ≤ p) ∨ (p < 20 ∧ 10 ≤ p) ∨ (p < 30 ∧ 20 ≤ p) ∨ (p < 40 ∧ 30 ≤ p) ∨ (p < 50 ∧ 40 ≤ p) ∨ (p < 60 ∧ 50 ≤ p) ∨ (p < 70 ∧ 60 ≤ p) ∨ (p < 80 ∧ 70 ≤ p) ∨ (p < 90 ∧ 80 ≤ p) ∨ (p < 101 ∧ 90 ≤ p) := by omega
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact bound_r66_g0 p h1 h2
    · exact bound_r66_g1 p h1 h2
    · exact bound_r66_g2 p h1 h2
    · exact bound_r66_g3 p h1 h2
    · exact bound_r66_g4 p h1 h2
    · exact bound_r66_g5 p h1 h2
    · exact bound_r66_g6 p h1 h2
    · exact bound_r66_g7 p h1 h2
    · exact bound_r66_g8 p h1 h2
    · exact bound_r66_g9 p h1 h2
  have hc : ∀ p : Nat, p < 101 → noClique (complementRows 101 rows_r66) p 5 ((2 ^ p - 1) &&& row (complementRows 101 rows_r66) p) = true := by
    intro p hp
    have hc : (p < 10 ∧ 0 ≤ p) ∨ (p < 20 ∧ 10 ≤ p) ∨ (p < 30 ∧ 20 ≤ p) ∨ (p < 40 ∧ 30 ≤ p) ∨ (p < 50 ∧ 40 ≤ p) ∨ (p < 60 ∧ 50 ≤ p) ∨ (p < 70 ∧ 60 ≤ p) ∨ (p < 80 ∧ 70 ≤ p) ∨ (p < 90 ∧ 80 ≤ p) ∨ (p < 101 ∧ 90 ≤ p) := by omega
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact bound_r66_c0 p h1 h2
    · exact bound_r66_c1 p h1 h2
    · exact bound_r66_c2 p h1 h2
    · exact bound_r66_c3 p h1 h2
    · exact bound_r66_c4 p h1 h2
    · exact bound_r66_c5 p h1 h2
    · exact bound_r66_c6 p h1 h2
    · exact bound_r66_c7 p h1 h2
    · exact bound_r66_c8 p h1 h2
    · exact bound_r66_c9 p h1 h2
  have h1 : noClique rows_r66 101 6 (fullMask 101) = true := noClique_chain rows_r66 5 101 hg
  have h2 : noClique (complementRows 101 rows_r66) 101 6 (fullMask 101) = true :=
    noClique_chain (complementRows 101 rows_r66) 5 101 hc
  exact ramsey_avoidance rows_r66 (by decide +kernel) h1 h2
