-- Prove2me | solution 1 for MarginalUtility.strictConcaveOn_of_diminishing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T23:24:45.818311+00:00
-- url     : https://prove2.me/submissions/5740c9c3-93a8-4e99-919b-ba5444853593

import Mathlib.Analysis.Convex.Deriv
import Definitions.Def_MarginalUtility_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology Set

open MarginalUtility

theorem solution (U : ℝ → ℝ) (D : Set ℝ)
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hU : HasDiminishingMarginalUtility U D) :
    StrictConcaveOn ℝ D U := by
  -- StrictConcaveOn from the negative second derivative:
  -- deriv^[2] U x is definitionally deriv (deriv U) x, the hypothesis
  -- gives its negativity on all of D, and D is open (interior D = D).
  have hinter : interior D = D := hDo.interior_eq
  refine strictConcaveOn_of_deriv2_neg hDc ?_ ?_
  · exact hU.1.continuousOn
  · intro x hx
    rw [hinter] at hx
    exact hU.2.2 x hx
