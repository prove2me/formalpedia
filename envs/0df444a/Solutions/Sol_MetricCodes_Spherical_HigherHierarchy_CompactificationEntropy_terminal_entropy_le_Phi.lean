-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy.terminal_entropy_le_Phi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/ee56f818-716c-42de-9872-8e41eb63869c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Phi_eq_sum_entropy_gaps
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_entropy_gap_nonneg

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
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
namespace MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) :
    MetricCodes.sphericalEntropy (a (Fin.last r)) ≤ Phi a b := by
  rw [Phi_eq_sum_entropy_gaps]
  have hsum : 0 ≤ ∑ i : Fin r,
      (MetricCodes.sphericalEntropy (a i.castSucc) -
        MetricCodes.sphericalEntropy (b i)) :=
    Finset.sum_nonneg fun i _ => entropy_gap_nonneg h i
  linarith
end MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
