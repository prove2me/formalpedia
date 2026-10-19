-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Interlacing.Phi_nonneg_refinement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/b7165f64-6853-48d5-ba49-f2de2faa6f59

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_strictMono
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_sub_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Phi_eq_sum_entropy_gaps

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
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
namespace Interlacing
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) : 0 ≤ Phi a b := by
  rw [Phi_eq_sum_entropy_gaps]
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro i _
    exact MetricCodes.Spherical.sphericalEntropy_sub_nonneg
      (h.stabilizer_pos i).le (h.2 i).1.le
  · have hmono := MetricCodes.Spherical.sphericalEntropy_strictMono.monotoneOn
      (show (0 : ℝ) ∈ Set.Ici 0 by simp)
      (show a (Fin.last r) ∈ Set.Ici 0 from h.1) h.1
    simpa [MetricCodes.sphericalEntropy] using hmono
end Interlacing
end MetricCodes.Spherical.HigherHierarchy
