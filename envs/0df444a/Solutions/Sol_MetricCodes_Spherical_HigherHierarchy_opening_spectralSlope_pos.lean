-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.opening_spectralSlope_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/5fabc751-83dc-4956-a66b-5556effd0d28

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_lagrangeWeight_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_openingContractionSpeed_pos

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
    (h : Interlacing a b) :
    0 < openingContractionSpeed a b *
        deriv (openingRegularGamma a b 1) 0 +
      lagrangeWeight a b (Fin.last r) := by
  let D : ℝ := deriv (openingRegularGamma a b 1) 0
  let w : ℝ := lagrangeWeight a b (Fin.last r)
  let η : ℝ := openingContractionSpeed a b
  have hw : 0 < w := h.lagrangeWeight_pos (Fin.last r)
  have hη : 0 < η := openingContractionSpeed_pos h
  have hidentity : 2 * η * (|D| + 1) = w := by
    dsimp [η, D, w, openingContractionSpeed]
    field_simp
  have hbound : -|D| ≤ D := neg_abs_le D
  have hηbound := mul_le_mul_of_nonneg_left hbound hη.le
  dsimp [η, D, w] at hidentity hηbound ⊢
  nlinarith [abs_nonneg (deriv (openingRegularGamma a b 1) 0)]
end MetricCodes.Spherical.HigherHierarchy
