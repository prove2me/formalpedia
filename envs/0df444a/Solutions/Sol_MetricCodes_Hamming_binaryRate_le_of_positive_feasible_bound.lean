-- Prove2me | solution 1 for MetricCodes.Hamming.binaryRate_le_of_positive_feasible_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/ec91b52b-2db0-4b82-9327-f2d0a0e34828

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_spectralPrefactor_pos
import Theorems.Thm_MetricCodes_Hamming_binaryRate_le_of_eventually_windowFibreQuotient

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution {δ a b : ℝ}
    (h : Feasible δ a b) (hb : 0 < b)
    (hbound : ∀ᶠ n : ℕ in atTop,
      (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) ≤
        spectralPrefactor δ a b * windowFibreQuotient a b n) :
    binaryRate δ ≤ MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b := by
  exact binaryRate_le_of_eventually_windowFibreQuotient
    hb h.2.1 h.2.2.1 (spectralPrefactor_pos h) hbound
end MetricCodes.Hamming
