-- Prove2me | solution 1 for GlobalTheory.AddLaw.addZ_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:12:26.171375+00:00
-- url     : https://prove2.me/submissions/aa7f4f66-d224-476b-8ea9-969cafef3868

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SubMulOriginD

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
variable {R : Type*} [CommRing R]
variable {W : Projective R}
namespace GlobalTheory.AddLaw
theorem _root_.solution (z₁ w₁ z₂ l : R) :
    W.addZ ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)] =
      l * W.addX ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)]
      - (w₁ - l * z₁) * W.negAddY ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)] := by
  simp only [addX, addZ, negAddY, fin3_def_ext]
  ring1
end GlobalTheory.AddLaw
