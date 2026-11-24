-- Prove2me | solution 1 for GlobalTheory.AddLaw.negDiagY_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:55:32.475542+00:00
-- url     : https://prove2.me/submissions/79f0879a-d3a4-49d4-9926-2ffbd5a75768

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY

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
    negDiagY W (u • P) (v • Q) = (u * v) ^ 2 * negDiagY W P Q := by
  simp only [negDiagY, smul_fin3_ext]
  ring1
end GlobalTheory.AddLaw
