-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy.entropy_gap_le_Phi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/a1ab30a1-7a1d-4cce-9bd3-0396fcc6ba59

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_strictMono
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
    (h : Interlacing a b) (i : Fin r) :
    MetricCodes.sphericalEntropy (a i.castSucc) -
        MetricCodes.sphericalEntropy (b i) ≤ Phi a b := by
  rw [Phi_eq_sum_entropy_gaps]
  have hterminal : 0 ≤ MetricCodes.sphericalEntropy (a (Fin.last r)) := by
    have hmono := MetricCodes.Spherical.sphericalEntropy_strictMono.monotoneOn
      (show (0 : ℝ) ∈ Set.Ici 0 by simp)
      (show a (Fin.last r) ∈ Set.Ici 0 from h.1) h.1
    simpa [MetricCodes.sphericalEntropy] using hmono
  have hsum :
      MetricCodes.sphericalEntropy (a i.castSucc) -
          MetricCodes.sphericalEntropy (b i) ≤
        ∑ j : Fin r,
          (MetricCodes.sphericalEntropy (a j.castSucc) -
            MetricCodes.sphericalEntropy (b j)) := by
    exact Finset.single_le_sum
      (fun j _ => entropy_gap_nonneg h j) (Finset.mem_univ i)
  linarith
end MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy
