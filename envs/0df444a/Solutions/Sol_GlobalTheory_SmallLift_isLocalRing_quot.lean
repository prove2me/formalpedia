-- Prove2me | solution 1 for GlobalTheory.SmallLift.isLocalRing_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:04:15.592353+00:00
-- url     : https://prove2.me/submissions/016dbbb7-c07e-499b-b891-88560ec7886f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsStalkRetractionOfSmallLifting
import Theorems.Thm_GlobalTheory_SmallLift_pow_ne_top

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
    IsLocalRing (A ⧸ maximalIdeal A ^ (n + 1)) :=
  haveI := Ideal.Quotient.nontrivial_iff.2 (pow_ne_top (A := A) n)
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
end GlobalTheory.SmallLift
