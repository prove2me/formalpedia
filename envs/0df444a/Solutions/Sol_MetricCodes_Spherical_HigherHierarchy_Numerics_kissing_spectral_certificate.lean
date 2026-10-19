-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Numerics.kissing_spectral_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/32f0fdce-942c-4ea7-85fd-103c2899a7a1

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Numerics_kissing_sqrt_lower

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchy.Numerics
namespace MetricCodes.Spherical.HigherHierarchy.Numerics
theorem _root_.solution :
    (0.00000212 : ℝ) <
      2 * Gamma kissingAmbient kissingStabilizer - (1 / 2 : ℝ) := by
  obtain ⟨h₀, h₁, h₂⟩ := kissing_sqrt_lower
  unfold Gamma
  rw [Fin.sum_univ_three]
  norm_num [spectralAtom, lagrangeWeight, lagrangeNumerator,
    lagrangeDenominator, quadraticCoordinate,
    Fin.prod_univ_two]
    at h₀ h₁ h₂ ⊢
  norm_num [Fin.ext_iff] at h₀ h₁ h₂ ⊢
  linarith
end MetricCodes.Spherical.HigherHierarchy.Numerics
