-- Prove2me | solution 1 for GlobalTheory.isPreconnected_polydisc_first_coords_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:42:17.818086+00:00
-- url     : https://prove2.me/submissions/a4b6d076-03c7-4f5d-a32a-6f4213a602cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPreconnectedPolydiscFirstCoordsNeZero
import Theorems.Thm_GlobalTheory_isPreconnected_punctured_unit_disc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (n a : ℕ) (ha : a ≤ n), _root_.IsPreconnected {z : Fin n → ℂ | z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0} := by
  intro n a ha
  have hS : {z : Fin n → ℂ | z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0}
      = Set.pi univ (fun k : Fin n => if (k:ℕ) < a then Metric.ball (0:ℂ) 1 \ {0} else Metric.ball (0:ℂ) 1) := by
    ext z
    rw [ball_pi _ one_pos]
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Pi.zero_apply]
    constructor
    · rintro ⟨hb, hne⟩ k
      split_ifs with hk
      · exact ⟨hb k, fun h => hne ⟨k, hk⟩ (by simpa using h)⟩
      · exact hb k
    · intro h
      refine ⟨fun k => ?_, fun i => ?_⟩
      · have := h k
        split_ifs at this
        · exact this.1
        · exact this
      · have := h (Fin.castLE ha i)
        rw [if_pos (by simp)] at this
        exact this.2
  rw [hS]
  apply isPreconnected_univ_pi
  intro k
  split_ifs
  · exact isPreconnected_punctured_unit_disc
  · exact (convex_ball (0:ℂ) 1).isPreconnected
end GlobalTheory
