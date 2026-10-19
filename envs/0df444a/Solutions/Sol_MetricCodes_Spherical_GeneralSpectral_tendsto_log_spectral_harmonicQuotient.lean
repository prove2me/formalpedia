-- Prove2me | solution 1 for MetricCodes.Spherical.GeneralSpectral.tendsto_log_spectral_harmonicQuotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/ab77d4be-1359-490a-875a-9cb4a6394192

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_spectralPrefactor_pos
import Theorems.Thm_SpherePacking_tendsto_log_const_mul_harmonicDimensionQuotient
import Theorems.Thm_MetricCodes_Spherical_GeneralSpectral_spectralPrefactor_pos
import Theorems.Thm_MetricCodes_Spherical_GeneralSpectral_legacy_binaryEntropy_eq_sphericalEntropy

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
    Tendsto
      (fun n : ℕ =>
        (Real.log
          (spectralPrefactor s a b *
            SpherePacking.harmonicDimensionQuotient a b n) /
          (n : ℝ)) / Real.log 2)
      atTop
      (nhds (MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b)) := by
  have ha : 0 < a := hb.trans hba
  have h := SpherePacking.tendsto_log_const_mul_harmonicDimensionQuotient
    a b (spectralPrefactor s a b) ha hb
    (spectralPrefactor_pos hs hspectral)
  rw [legacy_binaryEntropy_eq_sphericalEntropy a,
    legacy_binaryEntropy_eq_sphericalEntropy b] at h
  exact h
end MetricCodes.Spherical.GeneralSpectral
