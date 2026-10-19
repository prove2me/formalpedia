-- Prove2me | solution 1 for MetricCodes.Spherical.classicalPackingExponent_lt_packingExponent_of_maximizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/eb6975f6-976a-4573-bd61-4466d21dad5d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_classicalPackingObjective_lt_packingExponent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution
    {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hmax : ∀ t : ℝ, 0 < t → t < 1 →
      classicalPackingObjective t ≤ classicalPackingObjective s) :
    classicalPackingExponent < packingExponent := by
  have heq : classicalPackingExponent =
      (classicalPackingObjective s : EReal) := by
    apply le_antisymm
    · unfold classicalPackingExponent
      apply sSup_le
      rintro r ⟨t, ht, ht', rfl⟩
      exact EReal.coe_le_coe_iff.mpr (hmax t ht ht')
    · unfold classicalPackingExponent
      exact le_sSup ⟨s, hs, hs', rfl⟩
  rw [heq]
  exact classicalPackingObjective_lt_packingExponent hs hs'
end MetricCodes.Spherical
