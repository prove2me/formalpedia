-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.terminal_rayleigh_le_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/71607422-b54f-4356-a643-383b8fe99e18

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_terminalVector_ne_zero
import Theorems.Thm_MetricCodes_Hamming_terminalVector_rayleigh
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_terminalVector_ne_zero
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_terminalVector_rayleigh

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
    (n w p q L m : ℕ)
    (hfirst : p + q ≤ L) (hm : m ≤ L - (p + q)) :
    ((∑ r ∈ Finset.range (m + 1),
        MetricCodes.johnsonHattedDiagonal n w p q (L - m + r)) +
      2 * ∑ r ∈ Finset.range m,
        MetricCodes.johnsonHattedEdge n w p q (L - m + r)) /
      ((m : ℝ) + 1) ≤ MetricCodes.Johnson.topEigenvalue n w p q L := by
  rw [← terminalVector_rayleigh n w p q L m hfirst hm]
  exact MetricCodes.Johnson.rayleigh_le_top n w p q L
    (terminalVector p q L m) (terminalVector_ne_zero p q L m)
end MetricCodes.Johnson.SpectralAsymptotics
