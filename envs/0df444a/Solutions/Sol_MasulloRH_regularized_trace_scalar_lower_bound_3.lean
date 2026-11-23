-- Prove2me | solution 3 for MasulloRH.regularized_trace_scalar_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:20:45.974053+00:00
-- url     : https://prove2.me/submissions/cebf8c7d-0b53-4042-bfaf-85d5e58b8639
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_MasulloRH_single_resolvent_test
import Theorems.Thm_MasulloRH_regularized_initial_identity_full_strip
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

open MasulloRH

theorem solution (α : ℝ) (hα : 0 < α) (hsmall : α < 1/2) :
    (zetaLogDeriv 3).re ≤ (regularizedTraceRHS α 3).re := by
  rw [← MasulloRH.regularized_initial_identity_full_strip 3 (by norm_num)]
  refine (MasulloRH.single_resolvent_test α).mpr fun ρ => ?_
  rw [riemannHypothesis_iff_zeros_in_strip_on_line.mp mathlib_riemannHypothesis
    ρ.val ρ.2.1 ρ.2.2.1 ρ.2.2.2.1, sub_self, abs_zero]
  exact hα
