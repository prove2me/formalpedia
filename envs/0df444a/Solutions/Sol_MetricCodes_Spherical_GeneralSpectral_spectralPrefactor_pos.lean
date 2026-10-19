-- Prove2me | solution 1 for MetricCodes.Spherical.GeneralSpectral.spectralPrefactor_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/10b9d2ec-2f71-49d3-a5dd-70b0973d2805

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_spectralGap_pos
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_spectralGap_pos
import Theorems.Thm_MetricCodes_Spherical_GeneralSpectral_spectralGap_pos

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
theorem _root_.solution {s a b : ℝ}
    (hs : s < 1) (hgap : s < 2 * MetricCodes.Gamma a b) :
    0 < spectralPrefactor s a b := by
  unfold spectralPrefactor
  exact div_pos (sub_pos.mpr hs) (spectralGap_pos hgap)
end MetricCodes.Spherical.GeneralSpectral
