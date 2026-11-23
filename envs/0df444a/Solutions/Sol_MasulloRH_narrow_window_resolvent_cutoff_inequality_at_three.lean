-- Prove2me | solution 1 for MasulloRH.narrow_window_resolvent_cutoff_inequality_at_three
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:23:47.492548+00:00
-- url     : https://prove2.me/submissions/aef964ff-99f5-42a9-b3d1-57567d124392
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_MasulloRH_trace_formula_rational_iff_RH
import Theorems.Thm_MasulloRH_regularized_test_admissible

open MasulloRH Filter
set_option autoImplicit false
namespace MasulloRH
end MasulloRH
open MasulloRH

theorem solution
    (α : ℝ) (hα : 0 < α) (hα2 : α < 1 / 2)
    (hBoundary : ∀ z : ℂ, riemannZeta z = 0 → z.re = 1 / 2 + α → 0 < z.im → False) :
    ∃ᶠ n : ℕ in atTop,
      (cutoffPolar n (3 : ℂ) - cutoffSpectral α n (3 : ℂ)).re ≤
        (cutoffArch n (3 : ℂ) + cutoffPrime n (3 : ℂ)).re :=
  Filter.Frequently.of_forall fun n =>
    have h : cutoffArch n (3 : ℂ) + cutoffPrime n (3 : ℂ) =
        cutoffPolar n (3 : ℂ) - cutoffSpectral α n (3 : ℂ) :=
      (MasulloRH.trace_formula_rational_iff_RH.mpr mathlib_riemannHypothesis α hα
        (regularizedTraceTest n (3 : ℂ)) (MasulloRH.regularized_test_admissible n (3 : ℂ))).2.2.2
    le_of_eq (congrArg Complex.re h.symm)
