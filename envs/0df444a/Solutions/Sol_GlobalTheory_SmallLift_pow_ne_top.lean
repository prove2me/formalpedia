-- Prove2me | solution 1 for GlobalTheory.SmallLift.pow_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:50:20.115934+00:00
-- url     : https://prove2.me/submissions/d8e335cb-75f3-4d89-8ca4-1c286c54f3d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsStalkRetractionOfSmallLifting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.SmallLift
namespace GlobalTheory.SmallLift
theorem _root_.solution {A : Type} [CommRing A] [IsLocalRing A] (n : ℕ) :
    maximalIdeal A ^ (n + 1) ≠ ⊤ := fun h =>
  (maximalIdeal.isMaximal A).ne_top (top_le_iff.1 (h ▸ Ideal.pow_le_self n.succ_ne_zero))
end GlobalTheory.SmallLift
