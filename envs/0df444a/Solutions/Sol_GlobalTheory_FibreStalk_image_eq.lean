-- Prove2me | solution 1 for GlobalTheory.FibreStalk.image_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:53:45.646041+00:00
-- url     : https://prove2.me/submissions/8d536488-3d10-46ed-a226-446edff36bd9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RingKrullDimFiberStalkEqQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open GlobalTheory GlobalTheory.FibreStalk
namespace GlobalTheory.FibreStalk
theorem _root_.solution (B Y : Scheme.{0}) (π : Y ⟶ B) (b : B) (z : π.fiber b) : π (π.fiberι b z) = b := by
  have := (π.range_fiberι b).le ⟨z, rfl⟩
  simpa using this
end GlobalTheory.FibreStalk
