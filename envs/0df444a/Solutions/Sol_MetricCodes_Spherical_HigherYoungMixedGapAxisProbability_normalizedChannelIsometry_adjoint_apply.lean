-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungMixedGapAxisProbability.normalizedChannelIsometry_adjoint_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/7454194a-e241-41bf-901b-a136cc4a7971

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
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherYoungMixedGapAxisProbability
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherYoungMixedGapAxisProbability
theorem _root_.solution
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (A : E →ₗ[ℝ] F) (c : ℝ) (hc : 0 < c)
    (h : ∀ p q : E, ⟪A p, A q⟫_ℝ = c * ⟪p, q⟫_ℝ)
    (y : F) :
    (SpherePacking.HarmonicCoordinateOperators.normalizedChannelIsometry
      A c hc h).adjoint y =
        (Real.sqrt c)⁻¹ • A.adjoint y := by
  apply ext_inner_left ℝ
  intro x
  rw [LinearMap.adjoint_inner_right]
  change ⟪(Real.sqrt c)⁻¹ • A x, y⟫_ℝ =
    ⟪x, (Real.sqrt c)⁻¹ • A.adjoint y⟫_ℝ
  rw [real_inner_smul_left, real_inner_smul_right,
    LinearMap.adjoint_inner_right]
end MetricCodes.Spherical.HigherYoungMixedGapAxisProbability
