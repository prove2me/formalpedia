-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.hierarchyPackingObjective_le_hierarchyPackingExponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/361c7aec-fa38-4096-9e1a-38218abc8f30

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchy
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hpositive : 0 < Gamma a b) :
    (hierarchyPackingObjective a b : EReal) ≤ hierarchyPackingExponent := by
  exact le_sSup ⟨r, a, b, h, hpositive, rfl⟩
end MetricCodes.Spherical.HigherHierarchy
