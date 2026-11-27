-- Prove2me | solution 1 for GlobalTheory.T.ringKrullDim_fiber_stalk_eq_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:33:31.893912+00:00
-- url     : https://prove2.me/submissions/0d89bfc0-0a13-4400-a6b5-f76cf8a83e62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RingKrullDimFiberStalkEqQuotient
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RingKrullDimFiberStalkEqQuotientStatement
import Theorems.Thm_GlobalTheory_FibreStalk_ringKrullDim_stalk_fiber


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (b : B) (z : π.fiber b), ringKrullDim ((π.fiber b).presheaf.stalk z) = ringKrullDim (Y.presheaf.stalk (π.fiberι b z) ⧸ (IsLocalRing.maximalIdeal (B.presheaf.stalk (π (π.fiberι b z)))).map (π.stalkMap (π.fiberι b z)).hom) := by
  first | exact @GlobalTheory.FibreStalk.ringKrullDim_stalk_fiber | exact GlobalTheory.FibreStalk.ringKrullDim_stalk_fiber | (intros; apply GlobalTheory.FibreStalk.ringKrullDim_stalk_fiber <;> assumption)
end _root_.GlobalTheory.T
