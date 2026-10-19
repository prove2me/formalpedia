-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Interlacing.lagrangeDenominator_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/79dbb27f-42d3-4a37-a61f-5c1b51ab07b6

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_quadratic_injective

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
    lagrangeDenominator a ℓ ≠ 0 := by
  unfold lagrangeDenominator
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact sub_ne_zero.mpr
    (fun heq => Fin.ne_succAbove ℓ i (h.quadratic_injective heq))
end Interlacing
end MetricCodes.Spherical.HigherHierarchy
