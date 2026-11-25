-- Prove2me | solution 1 for GlobalTheory.FibreStalk.ringKrullDim_stalk_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:59:22.649951+00:00
-- url     : https://prove2.me/submissions/1e262dfe-06fa-429d-8e5c-965becad7b06

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RingKrullDimFiberStalkEqQuotient
import Theorems.Thm_GlobalTheory_FibreStalk_nonempty_ringEquiv_stalk_fiber

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
theorem _root_.solution : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (b : B) (z : π.fiber b),
    ringKrullDim ((π.fiber b).presheaf.stalk z) =
      ringKrullDim (Y.presheaf.stalk (π.fiberι b z) ⧸
        (IsLocalRing.maximalIdeal (B.presheaf.stalk (π (π.fiberι b z)))).map
          (π.stalkMap (π.fiberι b z)).hom) := by
  intro B Y π b z
  obtain ⟨e⟩ := nonempty_ringEquiv_stalk_fiber B Y π b z
  exact (ringKrullDim_eq_of_ringEquiv e).symm
end GlobalTheory.FibreStalk
