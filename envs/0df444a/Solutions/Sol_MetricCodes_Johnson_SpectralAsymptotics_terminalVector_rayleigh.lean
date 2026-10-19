-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.terminalVector_rayleigh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/7b65b070-4d0c-4290-8610-10d099fef9cf

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_terminalVector_norm_sq
import Theorems.Thm_MetricCodes_Hamming_terminalVector_inner
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_terminalVector_norm_sq
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_terminalVector_inner

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
    MetricCodes.Johnson.rayleigh n w p q L (terminalVector p q L m) =
      ((∑ r ∈ Finset.range (m + 1),
          MetricCodes.johnsonHattedDiagonal n w p q (L - m + r)) +
        2 * ∑ r ∈ Finset.range m,
          MetricCodes.johnsonHattedEdge n w p q (L - m + r)) /
        ((m : ℝ) + 1) := by
  rw [MetricCodes.Johnson.rayleigh_eq_inner,
    terminalVector_inner n w p q L m hfirst hm,
    terminalVector_norm_sq p q L m hm]
end MetricCodes.Johnson.SpectralAsymptotics
