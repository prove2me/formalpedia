-- Prove2me | solution 1 for MazurCampaign.no_order_eighteen
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T13:43:04.893426+00:00
-- url     : https://prove2.me/submissions/f9ec31c6-bcad-4d5a-afef-c3a87b5cb557

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints
import Theorems.Thm_MazurTransfer_order18_from_genus_two_exclusion
import Theorems.Thm_MazurTransfer_order18_no_noncuspidal_genus_two_point
open scoped WeierstrassCurve WeierstrassCurve.Affine

theorem solution (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ 18 := by
  intro x hx
  haveI : (E⁄ℚ).IsElliptic :=
    inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
  have horder : addOrderOf (x : (E⁄ℚ).Point) = addOrderOf x :=
    addOrderOf_injective (AddCommGroup.torsion (E⁄ℚ).Point).subtype
      (AddCommGroup.torsion (E⁄ℚ).Point).subtype_injective x
  exact MazurTransfer.order18_from_genus_two_exclusion E x
    MazurTransfer.order18_no_noncuspidal_genus_two_point (horder.trans hx)
#print axioms solution
