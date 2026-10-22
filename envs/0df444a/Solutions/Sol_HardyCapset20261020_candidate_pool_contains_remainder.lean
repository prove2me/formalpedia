-- Prove2me | solution 1 for HardyCapset20261020.candidate_pool_contains_remainder
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-20T13:33:46.971024+00:00
-- url     : https://prove2.me/submissions/6c2da02a-029b-4ee7-8c8e-08a27eb34fad

import Definitions.Def_HardyCapsetModel20261020
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum

open scoped BigOperators
set_option maxRecDepth 4096
set_option autoImplicit false
open HardyCapset20261020

theorem solution (A F : Finset Point)
    (hA : IsCap A) (hF : F ⊆ A) : A \ F ⊆ pool F := by
  intro q hq
  obtain ⟨hqA, hqF⟩ := Finset.mem_sdiff.mp hq
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, hqF, ?_⟩
  intro a ha b hb hab
  exact hA a (hF ha) b (hF hb) q hqA hab
    (fun he => hqF (he ▸ ha)) (fun he => hqF (he ▸ hb))
