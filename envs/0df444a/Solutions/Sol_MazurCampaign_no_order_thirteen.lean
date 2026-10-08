-- Prove2me | solution 1 for MazurCampaign.no_order_thirteen
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T15:17:19.054214+00:00
-- url     : https://prove2.me/submissions/79e0fe82-3763-49bb-bcd2-899f3dc27dd7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints
import Theorems.Thm_MazurTransfer_order13_from_genus_two_exclusion
import Theorems.Thm_MazurTransfer_order13_no_noncuspidal_genus_two_point
open scoped WeierstrassCurve WeierstrassCurve.Affine

theorem solution (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ 13 := by
  intro x hx
  haveI : (E⁄ℚ).IsElliptic :=
    inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
  have horder : addOrderOf (x : (E⁄ℚ).Point) = addOrderOf x :=
    addOrderOf_injective (AddCommGroup.torsion (E⁄ℚ).Point).subtype
      (AddCommGroup.torsion (E⁄ℚ).Point).subtype_injective x
  exact MazurTransfer.order13_from_genus_two_exclusion E x
    MazurTransfer.order13_no_noncuspidal_genus_two_point (horder.trans hx)
#print axioms solution
