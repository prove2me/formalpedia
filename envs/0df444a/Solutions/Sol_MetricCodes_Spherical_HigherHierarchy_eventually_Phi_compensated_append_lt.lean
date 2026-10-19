-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.eventually_Phi_compensated_append_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/e7661a13-bd18-41ce-bf01-60a21c7083fc

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_strictMono
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Phi_append
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compensatedScalingSlope_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compensatedPhiPath_differentiableAt_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_eventually_sub_sphericalEntropy_lt_of_differentiable
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_le_scaleCoordinate_of_one_le

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
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hlast : 0 < a (Fin.last r)) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      Phi
        (appendAmbient (scaleAmbient (compensatedScalingFactor a b ε) a))
        (appendStabilizer
          (scaleStabilizer (compensatedScalingFactor a b ε) b)
          (scaleCoordinate (compensatedScalingFactor a b ε) ε)) < Phi a b := by
  have hslope := compensatedScalingSlope_pos h hlast
  have hsmall := eventually_sub_sphericalEntropy_lt_of_differentiable
    (compensatedPhiPath_differentiableAt_zero h hlast)
  filter_upwards [hsmall, self_mem_nhdsWithin]
    with ε hεbound (hε : 0 < ε)
  let c : ℝ := compensatedScalingFactor a b ε
  have hquad : 0 < quadraticCoordinate ε := by
    unfold quadraticCoordinate
    positivity
  have hc : 1 ≤ c := by
    dsimp [c, compensatedScalingFactor]
    nlinarith
  have hcoordinate : ε ≤ scaleCoordinate c ε :=
    le_scaleCoordinate_of_one_le hc hε.le
  have hentropy :
      MetricCodes.sphericalEntropy ε ≤
        MetricCodes.sphericalEntropy (scaleCoordinate c ε) :=
    MetricCodes.Spherical.sphericalEntropy_strictMono.monotoneOn
      hε.le (scaleCoordinate_nonneg (by linarith) hε.le) hcoordinate
  rw [Phi_append]
  change compensatedPhiPath a b ε -
      MetricCodes.sphericalEntropy (scaleCoordinate c ε) < Phi a b
  rw [← compensatedPhiPath_zero h]
  linarith
end MetricCodes.Spherical.HigherHierarchy
