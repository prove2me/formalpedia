-- Prove2me | solution 1 for MarginalUtility.marginalUtility_strictAntiOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T23:24:25.529784+00:00
-- url     : https://prove2.me/submissions/48815e84-6398-4a17-93af-333c5d5fa20f

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Definitions.Def_MarginalUtility_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology Set

open MarginalUtility

theorem solution (U : ℝ → ℝ) (D : Set ℝ)
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hU : HasDiminishingMarginalUtility U D) :
    StrictAntiOn (marginalUtility U) D := by
  -- marginalUtility U is deriv U, D is open so interior D = D, and the
  -- diminishing-marginal-utility hypothesis says deriv (deriv U) < 0 on D.
  have hinter : interior D = D := hDo.interior_eq
  refine strictAntiOn_of_deriv_neg hDc ?_ ?_
  · exact hU.2.1.continuousOn
  · intro x hx
    rw [hinter] at hx
    exact hU.2.2 x hx
