-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.poleAngle_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/2f1b8464-d9ee-4234-ba92-ec0f22873034

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_poleAngle_eq_midpoint

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution {N : ℕ} (hN : 0 < N) (i : ℕ) :
    0 < poleAngle N i := by
  rw [poleAngle_eq_midpoint hN]
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  positivity
end MetricCodes.Spherical.HigherHierarchyChebyshev
