-- Prove2me | solution 2 for LinearChoresCLS.cls_membership
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:42:21.289422+00:00
-- url     : https://prove2.me/submissions/7d73811a-9ecd-4624-bf6f-57755bb8c82c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_LinearChoresCLS_ChoresSearch
import Theorems.Thm_LinearChoresCLS_chores_short_rational_ce
import Theorems.Thm_LinearChoresCLS_chores_ce_checkable
import Theorems.Thm_LinearChoresCLS_chores_cls_reduction_eventually

open NetworkEquilibriumCLS.LinearNash

theorem bounded_total_mono (S : SearchProblem) (k k' : ℕ) (hk : k ≤ k')
    (h : TotalSearch (bounded S k)) : TotalSearch (bounded S k') := by
  intro x hx
  obtain ⟨y, hy, hlen⟩ := h x hx
  refine ⟨y, hy, le_trans hlen ?_⟩
  have : (x.length + 1) ^ k ≤ (x.length + 1) ^ k' := Nat.pow_le_pow_right (by omega) hk
  omega

theorem solution : ∃ k : ℕ, InCLS (bounded LinearChoresCLS.choresCESearch k) := by
  obtain ⟨k0, hk0⟩ := LinearChoresCLS.chores_short_rational_ce
  obtain ⟨K, hK⟩ := LinearChoresCLS.chores_cls_reduction_eventually
  refine ⟨max k0 K, ⟨⟨bounded_total_mono _ _ _ (le_max_left _ _) hk0, ⟨max k0 K, ?_⟩,
    LinearChoresCLS.chores_ce_checkable _⟩, hK _ (le_max_right _ _)⟩⟩
  intro x y _ hy
  exact hy.2
