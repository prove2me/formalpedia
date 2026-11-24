-- Prove2me | solution 1 for GlobalTheory.AddLaw.map_diagXYZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:22:56.782319+00:00
-- url     : https://prove2.me/submissions/7900ab3f-18da-4cd9-9a99-7f251e10fcba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SubMulOriginD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Theorems.Thm_GlobalTheory_AddLaw_map_diagY
import Theorems.Thm_GlobalTheory_AddLaw_map_diagX
import Theorems.Thm_GlobalTheory_AddLaw_map_diagZ


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
theorem _root_.solution (f : R →+* S) (P Q : Fin 3 → R) :
    diagXYZ (W.map f) (f ∘ P) (f ∘ Q) = f ∘ diagXYZ W P Q := by
  simp only [diagXYZ, map_diagX, map_diagY, map_diagZ, comp_fin3]
end GlobalTheory.AddLaw
