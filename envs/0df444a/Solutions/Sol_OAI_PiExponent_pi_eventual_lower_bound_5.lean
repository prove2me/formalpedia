-- Prove2me | solution 5 for OAI.PiExponent.pi_eventual_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T06:15:12.104043+00:00
-- url     : https://prove2.me/submissions/480ecb27-593b-46dd-81c2-bb849eb9f6a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_rational_approximation_lower_bound
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open OAI.PiExponent

/-- The general rational approximation estimate is the eventual
lower-bound predicate specialised to pi. -/
theorem solution : PiEventualLowerBound := by
  change EventualLowerBound Real.pi
  intro nu hnu
  exact OAI.PiExponent.rational_approximation_lower_bound nu hnu
