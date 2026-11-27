-- Prove2me | solution 1 for GlobalTheory.bijective_standardAltForm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:35:42.766848+00:00
-- url     : https://prove2.me/submissions/6610821d-41b0-4874-94d5-b9e4716afe14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_isAlt_standardAltForm
import Theorems.Thm_GlobalTheory_isSymplecticBasisOfType_standardAltForm
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
theorem _root_.solution [Fintype ι] [DecidableEq ι] :
    Bijective (standardAltForm fun _ : ι => (1 : R)) :=
  IsSymplecticBasis.bijective (isSymplecticBasisOfType_standardAltForm _)
    (isAlt_standardAltForm _)
end GlobalTheory
