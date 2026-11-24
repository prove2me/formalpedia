-- Prove2me | solution 1 for GlobalTheory.AddLaw.diagXYZ_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:24:35.580455+00:00
-- url     : https://prove2.me/submissions/35718bf2-90ee-45a0-8d21-12a9aff0eb2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SubMulOriginD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Theorems.Thm_GlobalTheory_AddLaw_diagXYZ_X
import Theorems.Thm_GlobalTheory_AddLaw_diagXYZ_Y
import Theorems.Thm_GlobalTheory_AddLaw_diagXYZ_Z
import Theorems.Thm_GlobalTheory_AddLaw_diagY_smul
import Theorems.Thm_GlobalTheory_AddLaw_diagX_smul
import Theorems.Thm_GlobalTheory_AddLaw_diagZ_smul


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
theorem _root_.solution (P Q : Fin 3 → R) (u v : R) :
    diagXYZ W (u • P) (v • Q) = (u * v) ^ 2 • diagXYZ W P Q := by
  rw [diagXYZ, diagX_smul, diagY_smul, diagZ_smul, smul_fin3, diagXYZ_X, diagXYZ_Y, diagXYZ_Z]
end GlobalTheory.AddLaw
