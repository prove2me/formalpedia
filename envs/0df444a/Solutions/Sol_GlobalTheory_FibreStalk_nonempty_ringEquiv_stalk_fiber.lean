-- Prove2me | solution 1 for GlobalTheory.FibreStalk.nonempty_ringEquiv_stalk_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:41:32.356661+00:00
-- url     : https://prove2.me/submissions/35da8589-4aa0-4ed1-a7bc-1f1d65ab1f1c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RingKrullDimFiberStalkEqQuotient
import Theorems.Thm_P2M_GlobalTheory_FibreStalk_ker_stalkMap_fiber__bc23ea83ee2b

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
theorem _root_.solution (B Y : Scheme.{0}) (π : Y ⟶ B) (b : B) (z : π.fiber b) :
    Nonempty ((Y.presheaf.stalk (π.fiberι b z) ⧸
        (IsLocalRing.maximalIdeal (B.presheaf.stalk (π (π.fiberι b z)))).map
          (π.stalkMap (π.fiberι b z)).hom) ≃+* (π.fiber b).presheaf.stalk z) := by
  rw [← ker_stalkMap_fiberι]
  exact ⟨RingHom.quotientKerEquivOfSurjective ((π.fiberι b).stalkMap_surjective z)⟩
end GlobalTheory.FibreStalk
