-- Prove2me | solution 1 for MajorityAttack.NegCost.min_attack_power_lt
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:00:59.645318+00:00
-- url     : https://prove2.me/submissions/6b7eebab-7203-464e-b5bf-21f71fa42675

import Mathlib
import Definitions.Def_MajorityAttack_NegCost_Model

open MajorityAttack.NegCost in
theorem solution (H hstar : ℝ) (hH : 0 < H) (hhstar : 0 < hstar) :
    minAttackPower H hstar < H := by
  unfold minAttackPower
  exact max_lt (by linarith) (by linarith)
