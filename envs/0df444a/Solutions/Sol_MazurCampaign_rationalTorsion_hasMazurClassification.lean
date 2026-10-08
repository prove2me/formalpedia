-- Prove2me | solution 1 for MazurCampaign.rationalTorsion_hasMazurClassification
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T07:18:40.793893+00:00
-- url     : https://prove2.me/submissions/fd14a31b-debd-4f42-a6e3-05fb723cb422
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin

Reduction of the full canonical group classification to finiteness, allowed
point orders, and the seven subgroup exclusions from MazurTheorem.
-/
import Theorems.Thm_MazurCampaign_finite_group_classification
import Theorems.Thm_MazurCampaign_rational_torsion_finite
import Theorems.Thm_MazurCampaign_allowed_point_orders
import Theorems.Thm_MazurCampaign_rational_torsion_subgroup_obstructions

open scoped WeierstrassCurve.Affine

theorem solution (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    MazurCampaign.HasMazurClassification E := by
  letI : Finite (MazurCampaign.RationalTorsion E) :=
    (MazurCampaign.rational_torsion_finite E).to_subtype
  have horders : ∀ x : MazurCampaign.RationalTorsion E,
      addOrderOf x ∈ MazurCampaign.cyclicOrders := by
    intro x
    have hord : addOrderOf (x : (E⁄ℚ).Point) = addOrderOf x := by
      apply Nat.dvd_antisymm
      · exact addOrderOf_map_dvd
          (AddSubgroup.subtype (AddCommGroup.torsion (E⁄ℚ).Point)) x
      · apply addOrderOf_dvd_iff_nsmul_eq_zero.mpr
        apply Subtype.ext
        exact addOrderOf_nsmul_eq_zero (x : (E⁄ℚ).Point)
    rw [← hord]
    exact MazurCampaign.allowed_point_orders E x.val x.property
  exact MazurCampaign.finite_group_classification horders
    (MazurCampaign.rational_torsion_subgroup_obstructions E)
