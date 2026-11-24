-- Prove2me | solution 1 for GlobalTheory.AddLaw.negAddY_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:13:10.604049+00:00
-- url     : https://prove2.me/submissions/bf17e52c-a506-4f86-9362-f8adfce5baee

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
theorem _root_.solution {z₁ w₁ z₂ l : R} (h₁ : W.Equation ![z₁, -1, w₁])
    (hl : originN W z₁ w₁ z₂ = l * originD W w₁ z₂ (w₁ + l * (z₂ - z₁))) :
    (-lineQuadCoeff W l (w₁ - l * z₁) 1 - lineCubicCoeff W l 1 * (z₁ + z₂))
        * W.negAddY ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)]
      + lineCubicCoeff W l 1 * W.addX ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)] = 0 := by
  have h := sub_eq_zero.mpr <| (equation_iff _).mp h₁
  linear_combination (norm := (simp only [originN, originD, lineCubicCoeff, lineQuadCoeff, addX, negAddY, fin3_def_ext]; ring1))
    (-3 * z₁ - 3 * W.a₂ * z₁ * l - 3 * W.a₄ * z₁ * l ^ 2 - 3 * W.a₆ * z₁ * l ^ 3 + 3 * z₂
      + 3 * W.a₂ * l * z₂ + 3 * W.a₄ * l ^ 2 * z₂ + 3 * W.a₆ * l ^ 3 * z₂) * h
    + (-3 * z₁ ^ 2 - W.a₁ * z₁ * l - 2 * W.a₂ * z₁ ^ 2 * l - W.a₃ * z₁ * l ^ 2
      - W.a₄ * z₁ ^ 2 * l ^ 2 - W.a₂ * z₁ * w₁ - 2 * W.a₄ * z₁ * l * w₁
      - 3 * W.a₆ * z₁ * l ^ 2 * w₁ + 3 * z₁ * z₂ + W.a₁ * l * z₂ + 2 * W.a₂ * z₁ * l * z₂
      + W.a₃ * l ^ 2 * z₂ + W.a₄ * z₁ * l ^ 2 * z₂ + W.a₂ * w₁ * z₂ + 2 * W.a₄ * l * w₁ * z₂
      + 3 * W.a₆ * l ^ 2 * w₁ * z₂) * hl
end GlobalTheory.AddLaw
