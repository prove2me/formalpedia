-- Prove2me | solution 1 for LinearChoresCLS.epsQKKT_cls_membership
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:04:01.180799+00:00
-- url     : https://prove2.me/submissions/da1f3a28-4127-4f64-ac8a-1585412d6319
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_LinearChoresCLS_EpsKKT
import Theorems.Thm_LinearChoresCLS_epsQKKT_short_rational
import Theorems.Thm_LinearChoresCLS_epsQKKT_checkable
import Theorems.Thm_LinearChoresCLS_epsQKKT_cls_reduction

open NetworkEquilibriumCLS.LinearNash

theorem solution : ∃ k : ℕ, NetworkEquilibriumCLS.LinearNash.InCLS
    (NetworkEquilibriumCLS.LinearNash.bounded LinearChoresCLS.epsQKKTSearch k) := by
  obtain ⟨k, hk⟩ := LinearChoresCLS.epsQKKT_short_rational
  refine ⟨k, ⟨⟨hk, ⟨k, ?_⟩, LinearChoresCLS.epsQKKT_checkable k⟩, LinearChoresCLS.epsQKKT_cls_reduction k⟩⟩
  intro x y _hx hy
  exact hy.2
