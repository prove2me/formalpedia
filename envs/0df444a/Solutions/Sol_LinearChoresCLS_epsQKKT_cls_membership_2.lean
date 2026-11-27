-- Prove2me | solution 2 for LinearChoresCLS.epsQKKT_cls_membership
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:42:21.785906+00:00
-- url     : https://prove2.me/submissions/a0f1e160-d332-40ee-ad6b-ca6bebd883ee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_LinearChoresCLS_EpsKKT
import Theorems.Thm_LinearChoresCLS_epsQKKT_short_rational
import Theorems.Thm_LinearChoresCLS_epsQKKT_checkable
import Theorems.Thm_LinearChoresCLS_epsQKKT_cls_reduction_eventually

open NetworkEquilibriumCLS.LinearNash

theorem bounded_total_mono (S : SearchProblem) (k k' : ℕ) (hk : k ≤ k')
    (h : TotalSearch (bounded S k)) : TotalSearch (bounded S k') := by
  intro x hx
  obtain ⟨y, hy, hlen⟩ := h x hx
  refine ⟨y, hy, le_trans hlen ?_⟩
  have : (x.length + 1) ^ k ≤ (x.length + 1) ^ k' := Nat.pow_le_pow_right (by omega) hk
  omega

theorem solution : ∃ k : ℕ, InCLS (bounded LinearChoresCLS.epsQKKTSearch k) := by
  obtain ⟨k0, hk0⟩ := LinearChoresCLS.epsQKKT_short_rational
  obtain ⟨K, hK⟩ := LinearChoresCLS.epsQKKT_cls_reduction_eventually
  refine ⟨max k0 K, ⟨⟨bounded_total_mono _ _ _ (le_max_left _ _) hk0, ⟨max k0 K, ?_⟩,
    LinearChoresCLS.epsQKKT_checkable _⟩, hK _ (le_max_right _ _)⟩⟩
  intro x y _ hy
  exact hy.2
