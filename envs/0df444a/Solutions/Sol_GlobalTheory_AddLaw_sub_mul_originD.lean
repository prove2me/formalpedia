-- Prove2me | solution 1 for GlobalTheory.AddLaw.sub_mul_originD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:12:28.133048+00:00
-- url     : https://prove2.me/submissions/655d416e-ec39-41b7-809a-93007c7ef67c

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
theorem _root_.solution {z₁ w₁ z₂ w₂ : R} (h₁ : W.Equation ![z₁, -1, w₁])
    (h₂ : W.Equation ![z₂, -1, w₂]) :
    (w₂ - w₁) * originD W w₁ z₂ w₂ = (z₂ - z₁) * originN W z₁ w₁ z₂ := by
  have h := (equation_iff _).mp h₁
  have h' := (equation_iff _).mp h₂
  linear_combination (norm := (simp only [originN, originD, fin3_def_ext]; ring1)) h' - h
end GlobalTheory.AddLaw
