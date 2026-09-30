-- Prove2me | solution 1 for InventoryControl.two_level_cost_forms
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T20:30:04.661342+00:00
-- url     : https://prove2.me/submissions/1c94e715-aad0-4292-a969-6e34b6fdeadc

import Mathlib
import Definitions.Def_InventoryControl_serial

open InventoryControl in
theorem solution (d A1 A2 h1 h2 Q1 k : ℝ) (hk : k ≠ 0) (hQ : Q1 ≠ 0) :
    twoLevelCostInst d A1 A2 h1 h2 Q1 k = twoLevelCost d A1 A2 (h1 - h2) h2 Q1 k := by
  unfold twoLevelCostInst twoLevelCost eoqCost
  ring
