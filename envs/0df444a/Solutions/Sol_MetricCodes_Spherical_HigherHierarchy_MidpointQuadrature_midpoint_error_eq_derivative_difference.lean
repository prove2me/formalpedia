-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature.midpoint_error_eq_derivative_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/08af92c5-49b1-4451-ab97-9a9edad2745b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Set
open scoped Topology BigOperators
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature
namespace MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature
theorem _root_.solution
    {f g : ℝ → ℝ} {x y : ℝ} (hxy : x < y)
    (hf : ContinuousOn f (Set.Icc x y))
    (hderiv : ∀ z ∈ Set.Ioo x y, HasDerivAt f (g z) z) :
    ∃ u ∈ Set.Ioo x ((x + y) / 2),
      ∃ v ∈ Set.Ioo ((x + y) / 2) y,
        f ((x + y) / 2) - (f x + f y) / 2 =
          ((y - x) / 4) * (g u - g v) := by
  let m : ℝ := (x + y) / 2
  have hxm : x < m := by dsimp [m]; linarith
  have hmy : m < y := by dsimp [m]; linarith
  obtain ⟨u, hu, hfu⟩ := exists_hasDerivAt_eq_slope f g hxm
    (hf.mono (by intro z hz; exact ⟨hz.1, hz.2.trans hmy.le⟩))
    (by
      intro z hz
      exact hderiv z ⟨hz.1, hz.2.trans hmy⟩)
  obtain ⟨v, hv, hfv⟩ := exists_hasDerivAt_eq_slope f g hmy
    (hf.mono (by intro z hz; exact ⟨hxm.le.trans hz.1, hz.2⟩))
    (by
      intro z hz
      exact hderiv z ⟨hxm.trans hz.1, hz.2⟩)
  refine ⟨u, hu, v, hv, ?_⟩
  have hleft := (eq_div_iff (sub_ne_zero.mpr hxm.ne')).mp hfu
  have hright := (eq_div_iff (sub_ne_zero.mpr hmy.ne')).mp hfv
  dsimp [m] at hleft hright ⊢
  nlinarith
end MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature
