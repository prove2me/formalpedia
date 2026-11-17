-- Prove2me | solution 1 for MazurCampaign.hasRationalPointOfOrder_of_torsion
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:57.890242+00:00
-- url     : https://prove2.me/submissions/940c494e-f291-435b-800f-8fe4bb49e06b

import Definitions.Def_MazurCampaign_group_constraints
import Definitions.Def_TorsionDefs
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

open scoped WeierstrassCurve.Affine

namespace MazurCampaign

/-- The torsion subgroup inclusion preserves the exact additive order. -/
theorem _root_.solution
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (x : RationalTorsion E) (n : ℕ) (hx : addOrderOf x = n) :
    MazurProof.HasRationalPointOfOrder E n := by
  refine ⟨x.val, ?_⟩
  exact (addOrderOf_injective (AddCommGroup.torsion (E⁄ℚ).Point).subtype
    Subtype.val_injective x).trans hx

end MazurCampaign
