-- Prove2me | solution 1 for Leopoldt.isClosed_unitClosure
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:23:24.683216+00:00
-- url     : https://prove2.me/submissions/52811a0c-88bd-4b97-904b-7d5dbc0daccf

import Theorems.Thm_Leopoldt_isOpen_powMonoidHom_range

open Leopoldt in
theorem solution (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K] :
    IsClosed (unitClosure p K : Set (SemilocalUnits p K)) := by
  rw [unitClosure, Subgroup.coe_iInf]
  refine isClosed_iInter fun n => Subgroup.isClosed_of_isOpen _ ?_
  exact Subgroup.isOpen_mono le_sup_right (isOpen_powMonoidHom_range p K (n + 1))
