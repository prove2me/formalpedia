-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.terminalVector_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/bb87d067-cf4e-49fb-8182-a418363575e0

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_terminalVector_norm_sq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
open MetricCodes.Johnson.SpectralAsymptotics
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Johnson.Asymptotics
namespace MetricCodes.Johnson.SpectralAsymptotics
theorem _root_.solution
    (p q L m : ℕ) (hm : m ≤ L - (p + q)) :
    ‖terminalVector p q L m‖ ^ 2 = (m : ℝ) + 1 := by
  exact MetricCodes.Hamming.terminalVector_norm_sq (p + q) L m hm
end MetricCodes.Johnson.SpectralAsymptotics
