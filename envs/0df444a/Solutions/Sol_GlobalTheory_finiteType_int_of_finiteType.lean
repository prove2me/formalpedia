-- Prove2me | solution 1 for GlobalTheory.finiteType_int_of_finiteType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:11:49.420303+00:00
-- url     : https://prove2.me/submissions/6b17f0d2-dbf8-4523-9690-961cf715b1d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueExtensionOfForallNormLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing
namespace GlobalTheory
theorem _root_.solution (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType ℤ A] [Algebra.FiniteType A B] : Algebra.FiniteType ℤ B :=
  Algebra.FiniteType.trans (S := A) inferInstance inferInstance
end GlobalTheory
