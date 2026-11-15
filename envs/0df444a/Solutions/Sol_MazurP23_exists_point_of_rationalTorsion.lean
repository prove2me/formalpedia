-- Prove2me | solution 1 for MazurP23.exists_point_of_rationalTorsion
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T02:40:53.909512+00:00
-- url     : https://prove2.me/submissions/195d0d56-08df-42a7-ae57-642fcea2ef35

import Mathlib
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine
import Definitions.Def_MazurCampaign_target_objects

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine NNReal
universe u v

namespace MazurP23
theorem _root_.solution (E : WeierstrassCurve ℚ) {p : ℕ} (x : MazurCampaign.RationalTorsion E) (hx : addOrderOf x = p) : ∃ P : (E⁄ℚ).Point, addOrderOf P = p := by
  refine ⟨x, ?_⟩
  simpa only [AddSubgroup.addOrderOf_coe] using hx
end MazurP23
