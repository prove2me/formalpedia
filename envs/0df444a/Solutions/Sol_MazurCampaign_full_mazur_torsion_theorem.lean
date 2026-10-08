-- Prove2me | solution 1 for MazurCampaign.full_mazur_torsion_theorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-05T18:28:52.244736+00:00
-- url     : https://prove2.me/submissions/80f50ac1-4f7c-4fdd-9eba-de5711cdc272
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Theorems.Thm_MazurCampaign_rational_torsion_finite
import Theorems.Thm_MazurCampaign_rationalTorsion_hasMazurClassification
import Theorems.Thm_MazurCampaign_every_cyclic_group_occurs
import Theorems.Thm_MazurCampaign_every_bicyclic_group_occurs

open scoped WeierstrassCurve.Affine

theorem solution
    :
    (∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
      (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).Finite ∧
        MazurCampaign.HasMazurClassification E) ∧
    (∀ n ∈ MazurCampaign.cyclicOrders,
      ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧
        Nonempty (MazurCampaign.RationalTorsion E ≃+ ZMod n)) ∧
    (∀ m ∈ MazurCampaign.bicyclicParameters,
      ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧
        Nonempty (MazurCampaign.RationalTorsion E ≃+ (ZMod 2 × ZMod (2 * m)))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro E _
    exact ⟨MazurCampaign.rational_torsion_finite E,
      MazurCampaign.rationalTorsion_hasMazurClassification E⟩
  · exact MazurCampaign.every_cyclic_group_occurs
  · exact MazurCampaign.every_bicyclic_group_occurs
