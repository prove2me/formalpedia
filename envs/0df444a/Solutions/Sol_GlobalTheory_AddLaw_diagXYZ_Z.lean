-- Prove2me | solution 1 for GlobalTheory.AddLaw.diagXYZ_Z
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:54:09.280502+00:00
-- url     : https://prove2.me/submissions/e5d210cf-fd81-4bd2-a0df-54b2a1e0f1eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SubMulOriginD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open WeierstrassCurve WeierstrassCurve.Projective
open GlobalTheory GlobalTheory.AddLaw
variable {R S : Type*} [CommRing R] [CommRing S]
variable {W : Projective R}
namespace GlobalTheory.AddLaw
theorem _root_.solution (P Q : Fin 3 → R) : diagXYZ W P Q 2 = diagZ W P Q := rfl
end GlobalTheory.AddLaw
