-- Prove2me | solution 1 for MetricGenerators.IsometryExt.strong_is_metric_generator
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:58:18.479607+00:00
-- url     : https://prove2.me/submissions/d21777f3-6df5-46d6-b8d8-fe8df42318df

import Mathlib
import Definitions.Def_MetricGenerators_IsometryExt_Basic

set_option autoImplicit false
open MetricGenerators.IsometryExt

theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.Connected) (S : Finset V) (hS : IsStrongMetricGenerator G S) :
    IsMetricGenerator G S := by
  intro x y hxy
  obtain ⟨s, hs, h⟩ := hS x y
  refine ⟨s, hs, ?_⟩
  have hpos : 0 < G.dist y x := hG.pos_dist_of_ne (Ne.symm hxy)
  have hpos' : 0 < G.dist x y := hG.pos_dist_of_ne hxy
  intro heq
  rcases h with h | h <;> omega
