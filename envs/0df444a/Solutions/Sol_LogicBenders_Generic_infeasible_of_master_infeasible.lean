-- Prove2me | solution 1 for LogicBenders.Generic.infeasible_of_master_infeasible
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T01:54:14.510856+00:00
-- url     : https://prove2.me/submissions/406fbd26-bdfa-4592-bbc5-939ac1c9d87f

import Definitions.Def_LogicBenders_Generic_Setting
import Mathlib

open LogicBenders.Generic

theorem solution {X Y : Type*} (S : Set (X × Y)) (f : X → Y → ℝ)
    (cut : ℕ → Y → EReal) (k : ℕ) (hB1 : ∀ j ≤ k, ValidCut S f (cut j))
    (h : MasterInfeasible cut k) :
    S = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hle : masterLHS cut k p.2 ≤ (f p.1 p.2 : EReal) := by
    unfold masterLHS
    refine iSup_le fun j => iSup_le fun hj => ?_
    exact hB1 j (by simpa using Finset.mem_range.mp hj) p.1 p.2 hp
  rw [h p.2] at hle
  exact (EReal.coe_ne_top _) (top_le_iff.mp hle)
