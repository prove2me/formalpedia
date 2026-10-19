-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.hierarchyPackingExponent_le_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/51500c59-6228-469b-86da-06317124ea97

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
theorem _root_.solution {c : ℝ}
    (hupper : ∀ (r : ℕ) (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
      Interlacing a b → 0 < Gamma a b → hierarchyPackingObjective a b ≤ c) :
    hierarchyPackingExponent ≤ (c : EReal) := by
  unfold hierarchyPackingExponent
  apply sSup_le
  rintro _ ⟨r, a, b, h, hpositive, rfl⟩
  exact EReal.coe_le_coe_iff.mpr (hupper r a b h hpositive)
end MetricCodes.Spherical.HigherHierarchy
