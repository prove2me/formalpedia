-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Interlacing.lagrangeWeight_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/a7d990dd-c523-4ae6-88e4-0b62f6208d95

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_lagrangeFactor_pos

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchy
namespace MetricCodes.Spherical.HigherHierarchy
namespace Interlacing
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (ℓ : Fin (r + 1)) :
    0 < lagrangeWeight a b ℓ := by
  unfold lagrangeWeight lagrangeNumerator lagrangeDenominator
  rw [← Finset.prod_div_distrib]
  exact Finset.prod_pos fun i _ => h.lagrangeFactor_pos ℓ i
end Interlacing
end MetricCodes.Spherical.HigherHierarchy
