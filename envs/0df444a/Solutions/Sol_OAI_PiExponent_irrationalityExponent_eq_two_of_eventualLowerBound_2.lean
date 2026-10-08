-- Prove2me | solution 2 for OAI.PiExponent.irrationalityExponent_eq_two_of_eventualLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:21:55.195048+00:00
-- url     : https://prove2.me/submissions/367d02c9-9fb9-4e53-9b66-cfe5230211ee

import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Theorems.Thm_OAI_PiExponent_finite_goodRationalApproximations_of_eventualLowerBound
import Theorems.Thm_OAI_PiExponent_two_mem_approximationExponents

namespace OAI

namespace PiExponent

 













end PiExponent

end OAI

open OAI.PiExponent in
theorem solution {x : ℝ}
    (hi : Irrational x) (hx : EventualLowerBound x) :
    irrationalityExponent x = 2 := by
  have htwo := two_mem_approximationExponents hi
  have hbound : ∀ ν ∈ ApproximationExponents x, ν ≤ 2 := by
    intro ν hν
    by_contra h
    exact (finite_goodRationalApproximations_of_eventualLowerBound hx (by linarith)).not_infinite hν.2
  apply le_antisymm
  · exact csSup_le ⟨2, htwo⟩ hbound
  · exact le_csSup ⟨2, hbound⟩ htwo
