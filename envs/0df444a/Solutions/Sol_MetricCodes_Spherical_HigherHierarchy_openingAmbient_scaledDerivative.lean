-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.openingAmbient_scaledDerivative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/ac192072-b45a-4fd2-a73e-5a92d17c2988

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
    (a : Fin (r + 1) → ℝ) (η : ℝ) (i : Fin (r + 1)) :
    ScaledOpeningDerivative η
      (fun t => openingAmbient a (η * t) (t ^ 2) i)
      (fun t => openingAmbient a t (t ^ 2) i) := by
  unfold openingAmbient
  simp only [Function.update_apply]
  split_ifs
  · have hsq : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).fun_pow 2
    exact ⟨by simp, 0, by simpa using hsq, hsq⟩
  · refine ⟨by simp, -1, ?_, ?_⟩
    · simpa [mul_comm] using
        (hasDerivAt_const (0 : ℝ) (a 0)).fun_sub
          ((hasDerivAt_id (0 : ℝ)).const_mul η)
    · simpa using
        (hasDerivAt_const (0 : ℝ) (a 0)).fun_sub
          (hasDerivAt_id (0 : ℝ))
  · exact ScaledOpeningDerivative.const η (a i)
end MetricCodes.Spherical.HigherHierarchy
