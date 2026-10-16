-- Prove2me | solution 3 for OAI.PiExponent.pi_eventual_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T09:13:55.723737+00:00
-- url     : https://prove2.me/submissions/4a29e2b9-2b3b-4e37-874c-5188288a1cbd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_rational_approximation_lower_bound
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open OAI.PiExponent

theorem solution : PiEventualLowerBound := by
  intro nu hnu
  exact OAI.PiExponent.rational_approximation_lower_bound nu hnu
