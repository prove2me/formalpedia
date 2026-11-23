-- Prove2me | solution 4 for MasulloRH.regularized_initial_identity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:20:47.075575+00:00
-- url     : https://prove2.me/submissions/e514c31f-f1f3-48e1-8079-6d5d939c3538
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_MasulloRH_regularized_initial_identity_iff_scalar_bound
import Theorems.Thm_MasulloRH_single_resolvent_test
import Theorems.Thm_MasulloRH_regularized_initial_identity_full_strip
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace MasulloRH
end MasulloRH
open MasulloRH
theorem solution (α : ℝ) (hα : 0 < α) (hαsmall : α < 1 / 2)
    (s : ℂ) (hs : (3 / 2 : ℝ) < s.re) :
    regularizedTraceRHS α s = zetaLogDeriv s :=
  by
  -- Scalar bound at the point 3, proved from the Riemann hypothesis.
  have hscalar : (zetaLogDeriv 3).re ≤ (regularizedTraceRHS α 3).re := by
    -- The value of ζ'/ζ at 3 is the full-strip regularized trace at 3.
    rw [← MasulloRH.regularized_initial_identity_full_strip 3 (by norm_num)]
    -- Single-resolvent test: it suffices that every zero of the open strip lies in the window.
    refine (MasulloRH.single_resolvent_test α).mpr fun ρ => ?_
    -- Under RH the zero has real part 1/2, so its distance to the critical line is 0 < α.
    rw [riemannHypothesis_iff_zeros_in_strip_on_line.mp mathlib_riemannHypothesis
      ρ.val ρ.2.1 ρ.2.2.1 ρ.2.2.2.1, _root_.sub_self, _root_.abs_zero]
    exact hα
  -- The scalar bound is equivalent to the identity on the whole half-plane Re s > 3/2.
  exact (MasulloRH.regularized_initial_identity_iff_scalar_bound α).mpr hscalar s hs
