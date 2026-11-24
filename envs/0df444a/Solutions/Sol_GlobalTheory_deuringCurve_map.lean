-- Prove2me | solution 1 for GlobalTheory.deuringCurve_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:34:46.467948+00:00
-- url     : https://prove2.me/submissions/6a0af74c-f31b-4d12-ac7b-00a119552ce2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
variable {R : Type*} [CommRing R]
namespace GlobalTheory
theorem _root_.solution {S : Type*} [CommRing S] (f : R →+* S) (a b : R) :
    (deuringCurve a b).map f = deuringCurve (f a) (f b) := by
  simp [deuringCurve, WeierstrassCurve.map]
end GlobalTheory
