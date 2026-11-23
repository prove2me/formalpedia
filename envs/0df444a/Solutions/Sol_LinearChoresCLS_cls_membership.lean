-- Prove2me | solution 1 for LinearChoresCLS.cls_membership
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:22:14.060531+00:00
-- url     : https://prove2.me/submissions/06bed1fc-5e3f-46c6-a092-94508d8167aa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_LinearChoresCLS_ChoresSearch
import Theorems.Thm_LinearChoresCLS_chores_short_rational_ce
import Theorems.Thm_LinearChoresCLS_chores_ce_checkable
import Theorems.Thm_LinearChoresCLS_chores_cls_reduction

open NetworkEquilibriumCLS.LinearNash LinearChoresCLS

theorem solution : ∃ k : ℕ, InCLS (bounded choresCESearch k) := by
  obtain ⟨k, hk⟩ := chores_short_rational_ce
  refine ⟨k, ⟨⟨hk, ⟨k, ?_⟩, chores_ce_checkable k⟩, chores_cls_reduction k⟩⟩
  intro x y _hx hy
  exact hy.2
