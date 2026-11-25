-- Prove2me | solution 1 for GlobalTheory.SubmoduleSaturation.le_saturation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:13:33.287528+00:00
-- url     : https://prove2.me/submissions/64918600-3e91-4560-b7a6-978ef01bc720

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemSaturationOfPowSmulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SubmoduleSaturation
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
namespace GlobalTheory.SubmoduleSaturation
theorem _root_.solution (g : A) (K : Submodule A M) : K ≤ saturation g K :=
  fun m hm => ⟨0, by simpa using hm⟩
end GlobalTheory.SubmoduleSaturation
