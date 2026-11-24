-- Prove2me | solution 1 for GlobalTheory.SmallLift.isArtinianRing_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:17:08.537809+00:00
-- url     : https://prove2.me/submissions/4b6a8bf1-50c2-4833-b5b5-a98a87e17728

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsStalkRetractionOfSmallLifting
import Theorems.Thm_GlobalTheory_SmallLift_isLocalRing_quot
import Theorems.Thm_GlobalTheory_SmallLift_map_maximalIdeal_quot

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
theorem _root_.solution {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (n : ℕ) :
    IsArtinianRing (A ⧸ maximalIdeal A ^ (n + 1)) := by
  haveI := isLocalRing_quot (A := A) n
  rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
  refine ⟨n + 1, ?_⟩
  rw [← map_maximalIdeal_quot, ← Ideal.map_pow, Ideal.map_quotient_self]
  rfl
end GlobalTheory.SmallLift
