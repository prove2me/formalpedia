-- Prove2me | solution 1 for GlobalTheory.AddLaw.proportional_diagXYZ_addXYZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:09:23.800069+00:00
-- url     : https://prove2.me/submissions/f26795cf-5b1f-4270-a02e-28b7f6ff8e6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SubMulOriginD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Theorems.Thm_GlobalTheory_AddLaw_proportional_negY
import Theorems.Thm_GlobalTheory_AddLaw_diagX_mul_addZ
import Theorems.Thm_GlobalTheory_AddLaw_diagX_mul_negAddY
import Theorems.Thm_GlobalTheory_AddLaw_negDiagY_mul_addZ


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
theorem _root_.solution {P Q : Fin 3 → R} (hP : W.Equation P) (hQ : W.Equation Q) :
    Proportional (diagXYZ W P Q) (W.addXYZ P Q) :=
  proportional_negY W (diagX_mul_addZ hP hQ) (negDiagY_mul_addZ hP hQ) (diagX_mul_negAddY hP hQ)
end GlobalTheory.AddLaw
