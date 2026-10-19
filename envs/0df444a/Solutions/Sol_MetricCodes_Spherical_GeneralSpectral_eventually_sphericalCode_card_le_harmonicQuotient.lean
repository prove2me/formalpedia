-- Prove2me | solution 1 for MetricCodes.Spherical.GeneralSpectral.eventually_sphericalCode_card_le_harmonicQuotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/f31bd4d0-be36-43f2-be99-916976b000da

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_eventually_transverse_add_le_longitudinal
import Theorems.Thm_MetricCodes_Hamming_spectralGap_pos
import Theorems.Thm_MetricCodes_Hamming_spectralPrefactor_pos
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_spectralGap_pos
import Theorems.Thm_SpherePacking_truncatedDimensionQuotient_le_harmonicDimensionQuotient
import Theorems.Thm_MetricCodes_Spherical_GeneralSpectral_sphericalCode_bound_of_actual_harmonic_channels
import Theorems.Thm_MetricCodes_Spherical_GeneralSpectral_eventually_transverse_add_le_longitudinal
import Theorems.Thm_MetricCodes_Spherical_GeneralSpectral_spectralGap_pos
import Theorems.Thm_MetricCodes_Spherical_GeneralSpectral_eventually_topEigenvalue_uniform_gap
import Theorems.Thm_MetricCodes_Spherical_GeneralSpectral_spectralPrefactor_pos

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped BigOperators Nat Topology InnerProductSpace
open MetricCodes.Spherical.GeneralSpectral
namespace MetricCodes.Spherical.GeneralSpectral
theorem _root_.solution
    {s a b : ℝ} (hs : s < 1)
    (hb : 0 < b) (hba : b < a)
    (hspectral : s < 2 * MetricCodes.Gamma a b) :
    ∀ᶠ n : ℕ in atTop, ∀ C : SpherePacking.SphericalCode n s,
      (C.points.card : ℝ) ≤
        spectralPrefactor s a b *
          SpherePacking.harmonicDimensionQuotient a b n := by
  have hgap : 0 < spectralGap s a b := spectralGap_pos hspectral
  have hpref : 0 ≤ spectralPrefactor s a b :=
    (spectralPrefactor_pos hs hspectral).le
  filter_upwards [eventually_ge_atTop (3 : ℕ),
    eventually_transverse_add_le_longitudinal hb.le hba 1,
    eventually_topEigenvalue_uniform_gap hb.le hba hspectral]
      with n hn hdegrees heigen
  intro C
  have hkl : transverseDegree b n < longitudinalDegree a n := by omega
  have heigengap :
      s < SpherePacking.Jacobi.topEigenvalue
        n (transverseDegree b n) (longitudinalDegree a n) := by
    linarith
  have hactual := sphericalCode_bound_of_actual_harmonic_channels
    hn hkl hs.le heigengap C
  change
    (C.points.card : ℝ) ≤
      ((1 - s) /
        (SpherePacking.Jacobi.topEigenvalue
          n (transverseDegree b n) (longitudinalDegree a n) - s)) *
        SpherePacking.truncatedDimensionQuotient a b n at hactual
  have hden :
      0 < SpherePacking.Jacobi.topEigenvalue
        n (transverseDegree b n) (longitudinalDegree a n) - s := by
    linarith
  have hfrac :
      (1 - s) /
          (SpherePacking.Jacobi.topEigenvalue
            n (transverseDegree b n) (longitudinalDegree a n) - s) ≤
        spectralPrefactor s a b := by
    unfold spectralPrefactor
    apply (div_le_div_iff₀ hden hgap).2
    apply mul_le_mul_of_nonneg_left
    · linarith
    · linarith
  have htruncated :
      0 ≤ SpherePacking.truncatedDimensionQuotient a b n := by
    unfold SpherePacking.truncatedDimensionQuotient
    positivity
  calc
    (C.points.card : ℝ) ≤
      ((1 - s) /
        (SpherePacking.Jacobi.topEigenvalue
          n (transverseDegree b n) (longitudinalDegree a n) - s)) *
        SpherePacking.truncatedDimensionQuotient a b n := hactual
    _ ≤ spectralPrefactor s a b *
        SpherePacking.truncatedDimensionQuotient a b n :=
      mul_le_mul_of_nonneg_right hfrac htruncated
    _ ≤ spectralPrefactor s a b *
        SpherePacking.harmonicDimensionQuotient a b n :=
      mul_le_mul_of_nonneg_left
        (SpherePacking.truncatedDimensionQuotient_le_harmonicDimensionQuotient
          a b hn) hpref
end MetricCodes.Spherical.GeneralSpectral
