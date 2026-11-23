-- Prove2me | solution 1 for GlobalTheory.SmallLift.map_maximalIdeal_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:00:49.269819+00:00
-- url     : https://prove2.me/submissions/3f2dd440-f5c1-421c-9a02-4722c3dd4335

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
theorem _root_.solution {A : Type} [CommRing A] [IsLocalRing A] (J : Ideal A)
    [IsLocalRing (A ⧸ J)] :
    (maximalIdeal A).map (Ideal.Quotient.mk J) = maximalIdeal (A ⧸ J) :=
  IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
end GlobalTheory.SmallLift
