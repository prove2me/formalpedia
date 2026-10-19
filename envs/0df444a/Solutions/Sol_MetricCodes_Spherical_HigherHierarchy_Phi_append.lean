-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Phi_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/005cefe2-1f4b-4567-8e09-a6b2671b6392

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
theorem _root_.solution {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (ε : ℝ) :
    Phi (appendAmbient a) (appendStabilizer b ε) =
      Phi a b - MetricCodes.sphericalEntropy ε := by
  unfold Phi
  calc
    (∑ i : Fin (r + 2), MetricCodes.sphericalEntropy (appendAmbient a i)) -
          ∑ i : Fin (r + 1),
            MetricCodes.sphericalEntropy (appendStabilizer b ε i) =
        ((∑ i : Fin (r + 1), MetricCodes.sphericalEntropy (a i)) +
          MetricCodes.sphericalEntropy 0) -
          ((∑ i : Fin r, MetricCodes.sphericalEntropy (b i)) +
            MetricCodes.sphericalEntropy ε) := by
              congr 1
              · rw [Fin.sum_univ_castSucc]
                simp [appendAmbient]
              · rw [Fin.sum_univ_castSucc]
                simp [appendStabilizer]
    _ = (∑ i : Fin (r + 1), MetricCodes.sphericalEntropy (a i)) -
          (∑ i : Fin r, MetricCodes.sphericalEntropy (b i)) -
            MetricCodes.sphericalEntropy ε := by
              simp [MetricCodes.sphericalEntropy]
              ring
end MetricCodes.Spherical.HigherHierarchy
