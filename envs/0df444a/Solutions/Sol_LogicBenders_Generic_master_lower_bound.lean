-- Prove2me | solution 1 for LogicBenders.Generic.master_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T01:52:40.595284+00:00
-- url     : https://prove2.me/submissions/b46c3fec-d7ad-48a8-aeba-6ca7d772d4e7

import Definitions.Def_LogicBenders_Generic_Setting
import Mathlib

open LogicBenders.Generic

theorem solution {X Y : Type*} (S : Set (X × Y)) (f : X → Y → ℝ)
    (cut : ℕ → Y → EReal) (k : ℕ) (hB1 : ∀ j ≤ k, ValidCut S f (cut j))
    (z : EReal) (yb : Y) (h : IsMasterOptimal cut k z yb) :
    z ≤ optVal S f := by
  unfold optVal
  apply le_iInf
  intro p
  apply le_iInf
  intro hp
  apply (h.2.2 p.2).trans
  unfold masterLHS
  refine iSup_le fun j => iSup_le fun hj => ?_
  exact hB1 j (by simpa using Finset.mem_range.mp hj) p.1 p.2 hp
