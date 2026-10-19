-- Prove2me | solution 1 for MetricCodes.Spherical.GeneralSpectral.eventually_sphericalCode_card_lt_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/eb53c3da-6b45-433f-80b9-7f9aa523f211

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_spectralPrefactor_pos
import Theorems.Thm_SpherePacking_harmonicDimensionQuotient_pos
import Theorems.Thm_MetricCodes_Spherical_GeneralSpectral_spectralPrefactor_pos
import Theorems.Thm_MetricCodes_Spherical_GeneralSpectral_eventually_sphericalCode_card_le_harmonicQuotient
import Theorems.Thm_MetricCodes_Spherical_GeneralSpectral_tendsto_log_spectral_harmonicQuotient

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
    {s a b r : ℝ} (hs : s < 1)
    (hb : 0 < b) (hba : b < a)
    (hspectral : s < 2 * MetricCodes.Gamma a b)
    (hr : MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b < r) :
    ∀ᶠ n : ℕ in atTop, ∀ C : SpherePacking.SphericalCode n s,
      (C.points.card : ℝ) < (2 : ℝ) ^ (r * (n : ℝ)) := by
  have hlimit :=
    tendsto_log_spectral_harmonicQuotient hs hb hba hspectral
  have hrate :
      ∀ᶠ n : ℕ in atTop,
        (Real.log
          (spectralPrefactor s a b *
            SpherePacking.harmonicDimensionQuotient a b n) /
          (n : ℝ)) / Real.log 2 < r :=
    hlimit.eventually (Iio_mem_nhds hr)
  filter_upwards [
    eventually_sphericalCode_card_le_harmonicQuotient hs hb hba hspectral,
    hrate, eventually_ge_atTop (3 : ℕ)] with n hcode hnrate hn
  intro C
  have hnreal : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (by omega : 0 < n)
  have hlogtwo : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hpositive :
      0 < spectralPrefactor s a b *
        SpherePacking.harmonicDimensionQuotient a b n :=
    mul_pos (spectralPrefactor_pos hs hspectral)
      (SpherePacking.harmonicDimensionQuotient_pos a b hn)
  have hfirst :
      Real.log
        (spectralPrefactor s a b *
          SpherePacking.harmonicDimensionQuotient a b n) / (n : ℝ) <
        r * Real.log 2 :=
    (div_lt_iff₀ hlogtwo).mp hnrate
  have hsecond :
      Real.log
        (spectralPrefactor s a b *
          SpherePacking.harmonicDimensionQuotient a b n) <
        (r * Real.log 2) * (n : ℝ) :=
    (div_lt_iff₀ hnreal).mp hfirst
  calc
    (C.points.card : ℝ) ≤
      spectralPrefactor s a b *
        SpherePacking.harmonicDimensionQuotient a b n := hcode C
    _ = Real.exp
      (Real.log
        (spectralPrefactor s a b *
          SpherePacking.harmonicDimensionQuotient a b n)) :=
      (Real.exp_log hpositive).symm
    _ < Real.exp (Real.log 2 * (r * (n : ℝ))) := by
      apply Real.exp_lt_exp.mpr
      calc
        Real.log
          (spectralPrefactor s a b *
            SpherePacking.harmonicDimensionQuotient a b n) <
          (r * Real.log 2) * (n : ℝ) := hsecond
        _ = Real.log 2 * (r * (n : ℝ)) := by ring
    _ = (2 : ℝ) ^ (r * (n : ℝ)) :=
      (Real.rpow_def_of_pos (by norm_num) _).symm
end MetricCodes.Spherical.GeneralSpectral
