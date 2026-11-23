-- Prove2me | solution 1 for GlobalTheory.bijective_neg_bilinForm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:41.188065+00:00
-- url     : https://prove2.me/submissions/0d19d712-4834-44e7-8e0b-e26f81822311

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_bijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Function
open GlobalTheory
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {B : LinearMap.BilinForm R M}
namespace GlobalTheory
theorem _root_.solution (h : Bijective B) : Bijective (-B) :=
  neg_involutive.bijective.comp h
end GlobalTheory
