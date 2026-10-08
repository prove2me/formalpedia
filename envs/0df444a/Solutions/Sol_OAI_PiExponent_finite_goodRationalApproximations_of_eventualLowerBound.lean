-- Prove2me | solution 1 for OAI.PiExponent.finite_goodRationalApproximations_of_eventualLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:07:25.075978+00:00
-- url     : https://prove2.me/submissions/ff1540c7-c7d6-43b6-a02c-8e095125b2e2

import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Theorems.Thm_OAI_PiExponent_finite_rat_den_le_abs_sub_lt_one

namespace OAI

namespace PiExponent

 













end PiExponent

end OAI

open OAI.PiExponent in
theorem solution {x ν : ℝ}
    (hx : EventualLowerBound x) (hν : 2 < ν) :
    (GoodRationalApproximations x ν).Finite := by
  obtain ⟨Q, hQ, hb⟩ := hx ν hν
  apply (finite_rat_den_le_abs_sub_lt_one x Q).subset
  intro r hr
  have hltQ : r.den < Q := by
    by_contra h
    have h := hb r.num r.den (by omega)
    rw [← Rat.cast_def] at h
    exact (not_lt_of_ge h) hr.2.2
  refine ⟨hltQ.le, hr.2.2.trans_le ?_⟩
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast r.pos) (by linarith)
