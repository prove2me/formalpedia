-- Prove2me | solution 1 for GlobalTheory.ZModPerp.isPrincipalIdealRing_zmod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:40.851529+00:00
-- url     : https://prove2.me/submissions/bb8272ed-314a-4b99-93b8-68e9cb3f72ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_OrthogonalFreeOfPerfectAltZmod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TensorProduct
open GlobalTheory GlobalTheory.ZModPerp
namespace GlobalTheory.ZModPerp
theorem _root_.solution (n : ℕ) : IsPrincipalIdealRing (ZMod n) :=
  IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod n)) (ZMod.ringHom_surjective _)
end GlobalTheory.ZModPerp
