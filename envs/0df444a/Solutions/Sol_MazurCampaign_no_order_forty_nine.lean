-- Prove2me | solution 1 for MazurCampaign.no_order_forty_nine
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T06:08:47.336973+00:00
-- url     : https://prove2.me/submissions/99731919-d080-4979-81db-6fdd44963277

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints

import Theorems.Thm_MazurTransfer_order49_no_rational_affine_point

open scoped WeierstrassCurve.Affine

theorem solution (E : WeierstrassCurve ℚ) [E.IsElliptic] :
  ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ 49 := by
  intro x hx
  have : (E⁄ℚ).IsElliptic :=
    inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
  have horder : addOrderOf (x : (E⁄ℚ).Point) = addOrderOf x :=
    addOrderOf_injective (AddCommGroup.torsion (E⁄ℚ).Point).subtype
      (AddCommGroup.torsion (E⁄ℚ).Point).subtype_injective x
  exact MazurTransfer.order49_no_rational_affine_point (E⁄ℚ) (x : (E⁄ℚ).Point) (horder.trans hx)
#print axioms solution
