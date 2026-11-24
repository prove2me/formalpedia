-- Prove2me | solution 1 for GlobalTheory.AddLaw.negDiagY_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:12:27.145856+00:00
-- url     : https://prove2.me/submissions/25d6cce4-b903-4040-adfc-c80bf7624f2d

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
        * negDiagY W ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)]
      + lineCubicCoeff W l 1 * diagX W ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)] = 0 := by
  have h := sub_eq_zero.mpr <| (equation_iff _).mp h₁
  linear_combination (norm := (simp only [originN, originD, lineCubicCoeff, lineQuadCoeff, diagX, negDiagY, fin3_def_ext]; ring1))
    (W.a₁ ^ 2 + W.a₂ - 3 * W.a₃ * z₁ - 6 * W.a₂ ^ 2 * z₁ ^ 2 + 6 * W.a₂ ^ 2 * l
      + 3 * W.a₁ * W.a₃ * l + 3 * W.a₄ * l + W.a₁ ^ 2 * W.a₃ * z₁ * l - 2 * W.a₂ * W.a₃ * z₁ * l
      - 3 * W.a₃ ^ 2 * z₁ ^ 2 * l + W.a₁ ^ 2 * W.a₄ * z₁ ^ 2 * l - 5 * W.a₂ * W.a₄ * z₁ ^ 2 * l
      - 9 * W.a₆ * z₁ ^ 2 * l + 3 * W.a₃ ^ 2 * l ^ 2 + 6 * W.a₂ * W.a₄ * l ^ 2 + 9 * W.a₆ * l ^ 2
      + 6 * W.a₂ ^ 2 * W.a₃ * z₁ * l ^ 2 + 3 * W.a₁ * W.a₃ ^ 2 * z₁ * l ^ 2
      - 3 * W.a₂ * W.a₃ ^ 2 * z₁ ^ 2 * l ^ 2 + 3 * W.a₁ * W.a₃ * W.a₄ * z₁ ^ 2 * l ^ 2
      + 3 * W.a₄ ^ 2 * z₁ ^ 2 * l ^ 2 - 9 * W.a₂ * W.a₆ * z₁ ^ 2 * l ^ 2 + W.a₂ * W.a₃ ^ 2 * l ^ 3
      - W.a₁ * W.a₃ * W.a₄ * l ^ 3 - W.a₄ ^ 2 * l ^ 3 + W.a₁ ^ 2 * W.a₆ * l ^ 3
      + 4 * W.a₂ * W.a₆ * l ^ 3 + 3 * W.a₃ ^ 3 * z₁ * l ^ 3 + 6 * W.a₂ * W.a₃ * W.a₄ * z₁ * l ^ 3
      + 6 * W.a₃ * W.a₆ * z₁ * l ^ 3 - 6 * W.a₂ ^ 2 * W.a₆ * z₁ ^ 2 * l ^ 3
      + W.a₂ * W.a₃ ^ 3 * z₁ * l ^ 4 - W.a₁ * W.a₃ ^ 2 * W.a₄ * z₁ * l ^ 4
      - W.a₃ * W.a₄ ^ 2 * z₁ * l ^ 4 + W.a₁ ^ 2 * W.a₃ * W.a₆ * z₁ * l ^ 4
      + 4 * W.a₂ * W.a₃ * W.a₆ * z₁ * l ^ 4 + W.a₂ * W.a₃ ^ 2 * W.a₄ * z₁ ^ 2 * l ^ 4
      - W.a₁ * W.a₃ * W.a₄ ^ 2 * z₁ ^ 2 * l ^ 4 - W.a₄ ^ 3 * z₁ ^ 2 * l ^ 4
      - 3 * W.a₃ ^ 2 * W.a₆ * z₁ ^ 2 * l ^ 4 + W.a₁ ^ 2 * W.a₄ * W.a₆ * z₁ ^ 2 * l ^ 4
      - 2 * W.a₂ * W.a₄ * W.a₆ * z₁ ^ 2 * l ^ 4 - 9 * W.a₆ ^ 2 * z₁ ^ 2 * l ^ 4
      - 6 * W.a₁ * W.a₂ ^ 2 * w₁ - 2 * W.a₁ ^ 2 * W.a₃ * w₁ - 2 * W.a₂ * W.a₃ * w₁
      - 6 * W.a₂ ^ 3 * z₁ * w₁ + 3 * W.a₃ ^ 2 * z₁ * w₁ - W.a₁ ^ 2 * W.a₄ * z₁ * w₁
      - W.a₂ * W.a₄ * z₁ * w₁ + 9 * W.a₆ * z₁ * w₁ - 12 * W.a₂ ^ 2 * W.a₃ * l * w₁
      - 6 * W.a₁ * W.a₃ ^ 2 * l * w₁ - 6 * W.a₁ * W.a₂ * W.a₄ * l * w₁ - 6 * W.a₃ * W.a₄ * l * w₁
      - 6 * W.a₂ ^ 2 * W.a₄ * z₁ * l * w₁ - 6 * W.a₃ ^ 3 * l ^ 2 * w₁
      - 12 * W.a₂ * W.a₃ * W.a₄ * l ^ 2 * w₁ - 18 * W.a₃ * W.a₆ * l ^ 2 * w₁
      - 3 * W.a₂ ^ 2 * W.a₃ ^ 2 * z₁ * l ^ 2 * w₁
      + 3 * W.a₁ * W.a₂ * W.a₃ * W.a₄ * z₁ * l ^ 2 * w₁ + 3 * W.a₂ * W.a₄ ^ 2 * z₁ * l ^ 2 * w₁
      - 3 * W.a₁ ^ 2 * W.a₂ * W.a₆ * z₁ * l ^ 2 * w₁ + 6 * W.a₂ ^ 2 * W.a₆ * z₁ * l ^ 2 * w₁
      + 9 * W.a₁ * W.a₃ * W.a₆ * z₁ * l ^ 2 * w₁ + 9 * W.a₄ * W.a₆ * z₁ * l ^ 2 * w₁
      - 2 * W.a₂ * W.a₃ ^ 3 * l ^ 3 * w₁ + 2 * W.a₁ * W.a₃ ^ 2 * W.a₄ * l ^ 3 * w₁
      + 2 * W.a₃ * W.a₄ ^ 2 * l ^ 3 * w₁ - 2 * W.a₁ ^ 2 * W.a₃ * W.a₆ * l ^ 3 * w₁
      - 8 * W.a₂ * W.a₃ * W.a₆ * l ^ 3 * w₁ - 4 * W.a₂ * W.a₃ ^ 2 * W.a₄ * z₁ * l ^ 3 * w₁
      + 4 * W.a₁ * W.a₃ * W.a₄ ^ 2 * z₁ * l ^ 3 * w₁ + 4 * W.a₄ ^ 3 * z₁ * l ^ 3 * w₁
      + 12 * W.a₃ ^ 2 * W.a₆ * z₁ * l ^ 3 * w₁ - 4 * W.a₁ ^ 2 * W.a₄ * W.a₆ * z₁ * l ^ 3 * w₁
      + 2 * W.a₂ * W.a₄ * W.a₆ * z₁ * l ^ 3 * w₁ + 36 * W.a₆ ^ 2 * z₁ * l ^ 3 * w₁
      + 3 * W.a₂ * W.a₃ ^ 2 * w₁ ^ 2 - 6 * W.a₂ ^ 2 * W.a₄ * w₁ ^ 2
      - 3 * W.a₁ * W.a₃ * W.a₄ * w₁ ^ 2 - 3 * W.a₄ ^ 2 * w₁ ^ 2 + 9 * W.a₂ * W.a₆ * w₁ ^ 2
      + 3 * W.a₂ ^ 2 * W.a₃ ^ 2 * l * w₁ ^ 2 - 3 * W.a₁ * W.a₂ * W.a₃ * W.a₄ * l * w₁ ^ 2
      - 9 * W.a₂ * W.a₄ ^ 2 * l * w₁ ^ 2 + 3 * W.a₁ ^ 2 * W.a₂ * W.a₆ * l * w₁ ^ 2
      - 6 * W.a₂ ^ 2 * W.a₆ * l * w₁ ^ 2 - 9 * W.a₁ * W.a₃ * W.a₆ * l * w₁ ^ 2
      - 9 * W.a₄ * W.a₆ * l * w₁ ^ 2 + 3 * W.a₂ * W.a₃ ^ 2 * W.a₄ * l ^ 2 * w₁ ^ 2
      - 3 * W.a₁ * W.a₃ * W.a₄ ^ 2 * l ^ 2 * w₁ ^ 2 - 3 * W.a₄ ^ 3 * l ^ 2 * w₁ ^ 2
      - 9 * W.a₃ ^ 2 * W.a₆ * l ^ 2 * w₁ ^ 2 + 3 * W.a₁ ^ 2 * W.a₄ * W.a₆ * l ^ 2 * w₁ ^ 2
      - 6 * W.a₂ * W.a₄ * W.a₆ * l ^ 2 * w₁ ^ 2 - 27 * W.a₆ ^ 2 * l ^ 2 * w₁ ^ 2 - W.a₁ ^ 3 * z₂
      - W.a₁ * W.a₂ * z₂ - W.a₁ ^ 2 * W.a₂ * z₁ * z₂ - 7 * W.a₂ ^ 2 * z₁ * z₂
      + 3 * W.a₁ * W.a₃ * z₁ * z₂ + 3 * W.a₄ * z₁ * z₂ - 6 * W.a₁ * W.a₂ ^ 2 * l * z₂
      - 4 * W.a₁ ^ 2 * W.a₃ * l * z₂ - W.a₂ * W.a₃ * l * z₂ - 3 * W.a₁ * W.a₄ * l * z₂
      + 3 * W.a₃ ^ 2 * z₁ * l * z₂ - W.a₁ ^ 2 * W.a₄ * z₁ * l * z₂ - 7 * W.a₂ * W.a₄ * z₁ * l * z₂
      + 9 * W.a₆ * z₁ * l * z₂ - 6 * W.a₂ ^ 2 * W.a₃ * l ^ 2 * z₂
      - 6 * W.a₁ * W.a₃ ^ 2 * l ^ 2 * z₂ - 6 * W.a₁ * W.a₂ * W.a₄ * l ^ 2 * z₂
      - 3 * W.a₃ * W.a₄ * l ^ 2 * z₂ - 9 * W.a₁ * W.a₆ * l ^ 2 * z₂
      + 6 * W.a₂ ^ 2 * W.a₄ * z₁ * l ^ 2 * z₂ - W.a₁ * W.a₂ * W.a₃ ^ 2 * l ^ 3 * z₂
      - 3 * W.a₃ ^ 3 * l ^ 3 * z₂ + W.a₁ ^ 2 * W.a₃ * W.a₄ * l ^ 3 * z₂
      - 6 * W.a₂ * W.a₃ * W.a₄ * l ^ 3 * z₂ + W.a₁ * W.a₄ ^ 2 * l ^ 3 * z₂
      - W.a₁ ^ 3 * W.a₆ * l ^ 3 * z₂ - 4 * W.a₁ * W.a₂ * W.a₆ * l ^ 3 * z₂
      - 9 * W.a₃ * W.a₆ * l ^ 3 * z₂ - W.a₂ ^ 2 * W.a₃ ^ 2 * z₁ * l ^ 3 * z₂
      + W.a₁ * W.a₂ * W.a₃ * W.a₄ * z₁ * l ^ 3 * z₂ + 7 * W.a₂ * W.a₄ ^ 2 * z₁ * l ^ 3 * z₂
      - W.a₁ ^ 2 * W.a₂ * W.a₆ * z₁ * l ^ 3 * z₂ + 8 * W.a₂ ^ 2 * W.a₆ * z₁ * l ^ 3 * z₂
      + 3 * W.a₁ * W.a₃ * W.a₆ * z₁ * l ^ 3 * z₂ + 3 * W.a₄ * W.a₆ * z₁ * l ^ 3 * z₂
      - W.a₂ * W.a₃ ^ 3 * l ^ 4 * z₂ + W.a₁ * W.a₃ ^ 2 * W.a₄ * l ^ 4 * z₂
      + W.a₃ * W.a₄ ^ 2 * l ^ 4 * z₂ - W.a₁ ^ 2 * W.a₃ * W.a₆ * l ^ 4 * z₂
      - 4 * W.a₂ * W.a₃ * W.a₆ * l ^ 4 * z₂ - W.a₂ * W.a₃ ^ 2 * W.a₄ * z₁ * l ^ 4 * z₂
      + W.a₁ * W.a₃ * W.a₄ ^ 2 * z₁ * l ^ 4 * z₂ + W.a₄ ^ 3 * z₁ * l ^ 4 * z₂
      + 3 * W.a₃ ^ 2 * W.a₆ * z₁ * l ^ 4 * z₂ - W.a₁ ^ 2 * W.a₄ * W.a₆ * z₁ * l ^ 4 * z₂
      + 8 * W.a₂ * W.a₄ * W.a₆ * z₁ * l ^ 4 * z₂ + 9 * W.a₆ ^ 2 * z₁ * l ^ 4 * z₂
      - 6 * W.a₂ ^ 3 * w₁ * z₂ + 3 * W.a₃ ^ 2 * w₁ * z₂ - W.a₁ ^ 2 * W.a₄ * w₁ * z₂
      - W.a₂ * W.a₄ * w₁ * z₂ + 9 * W.a₆ * w₁ * z₂ + 6 * W.a₂ * W.a₃ ^ 2 * l * w₁ * z₂
      - 18 * W.a₂ ^ 2 * W.a₄ * l * w₁ * z₂ - 6 * W.a₁ * W.a₃ * W.a₄ * l * w₁ * z₂
      - 6 * W.a₄ ^ 2 * l * w₁ * z₂ + 18 * W.a₂ * W.a₆ * l * w₁ * z₂
      + 3 * W.a₂ ^ 2 * W.a₃ ^ 2 * l ^ 2 * w₁ * z₂
      - 3 * W.a₁ * W.a₂ * W.a₃ * W.a₄ * l ^ 2 * w₁ * z₂ - 15 * W.a₂ * W.a₄ ^ 2 * l ^ 2 * w₁ * z₂
      + 3 * W.a₁ ^ 2 * W.a₂ * W.a₆ * l ^ 2 * w₁ * z₂ - 6 * W.a₂ ^ 2 * W.a₆ * l ^ 2 * w₁ * z₂
      - 9 * W.a₁ * W.a₃ * W.a₆ * l ^ 2 * w₁ * z₂ - 9 * W.a₄ * W.a₆ * l ^ 2 * w₁ * z₂
      + 2 * W.a₂ * W.a₃ ^ 2 * W.a₄ * l ^ 3 * w₁ * z₂
      - 2 * W.a₁ * W.a₃ * W.a₄ ^ 2 * l ^ 3 * w₁ * z₂ - 2 * W.a₄ ^ 3 * l ^ 3 * w₁ * z₂
      - 6 * W.a₃ ^ 2 * W.a₆ * l ^ 3 * w₁ * z₂ + 2 * W.a₁ ^ 2 * W.a₄ * W.a₆ * l ^ 3 * w₁ * z₂
      - 10 * W.a₂ * W.a₄ * W.a₆ * l ^ 3 * w₁ * z₂ - 18 * W.a₆ ^ 2 * l ^ 3 * w₁ * z₂
      - 6 * W.a₂ ^ 2 * z₂ ^ 2 - 6 * W.a₂ ^ 3 * l * z₂ ^ 2 - 6 * W.a₂ * W.a₄ * l * z₂ ^ 2
      - 12 * W.a₂ ^ 2 * W.a₄ * l ^ 2 * z₂ ^ 2 - 6 * W.a₂ * W.a₄ ^ 2 * l ^ 3 * z₂ ^ 2
      - 6 * W.a₂ ^ 2 * W.a₆ * l ^ 3 * z₂ ^ 2 - 6 * W.a₂ * W.a₄ * W.a₆ * l ^ 4 * z₂ ^ 2) * h
    + (-W.a₁ + W.a₁ ^ 2 * z₁ + W.a₂ * z₁ - 3 * W.a₃ * z₁ ^ 2 - 6 * W.a₂ ^ 2 * z₁ ^ 3 - W.a₃ * l
      + 2 * W.a₄ * z₁ * l + W.a₁ ^ 2 * W.a₃ * z₁ ^ 2 * l - W.a₂ * W.a₃ * z₁ ^ 2 * l
      - W.a₁ * W.a₄ * z₁ ^ 2 * l - 3 * W.a₃ ^ 2 * z₁ ^ 3 * l + W.a₁ ^ 2 * W.a₄ * z₁ ^ 3 * l
      - 5 * W.a₂ * W.a₄ * z₁ ^ 3 * l - 9 * W.a₆ * z₁ ^ 3 * l - W.a₃ ^ 2 * z₁ * l ^ 2
      + 3 * W.a₆ * z₁ * l ^ 2 + W.a₁ * W.a₃ ^ 2 * z₁ ^ 2 * l ^ 2
      - 3 * W.a₁ * W.a₆ * z₁ ^ 2 * l ^ 2 - 2 * W.a₂ * W.a₃ ^ 2 * z₁ ^ 3 * l ^ 2
      + 2 * W.a₁ * W.a₃ * W.a₄ * z₁ ^ 3 * l ^ 2 + 2 * W.a₄ ^ 2 * z₁ ^ 3 * l ^ 2
      - 6 * W.a₂ * W.a₆ * z₁ ^ 3 * l ^ 2 + 6 * W.a₂ ^ 2 * w₁ + 3 * W.a₁ * W.a₃ * w₁ + W.a₄ * w₁
      - 6 * W.a₁ * W.a₂ ^ 2 * z₁ * w₁ - 2 * W.a₁ ^ 2 * W.a₃ * z₁ * w₁ - 3 * W.a₂ * W.a₃ * z₁ * w₁
      + W.a₁ * W.a₄ * z₁ * w₁ - 6 * W.a₂ ^ 3 * z₁ ^ 2 * w₁ + 3 * W.a₃ ^ 2 * z₁ ^ 2 * w₁
      - W.a₁ ^ 2 * W.a₄ * z₁ ^ 2 * w₁ - W.a₂ * W.a₄ * z₁ ^ 2 * w₁ + 9 * W.a₆ * z₁ ^ 2 * w₁
      + 4 * W.a₃ ^ 2 * l * w₁ + 6 * W.a₂ * W.a₄ * l * w₁ + 6 * W.a₆ * l * w₁
      - 2 * W.a₁ * W.a₃ ^ 2 * z₁ * l * w₁ - 6 * W.a₁ * W.a₂ * W.a₄ * z₁ * l * w₁
      - 4 * W.a₃ * W.a₄ * z₁ * l * w₁ - 2 * W.a₂ * W.a₃ ^ 2 * z₁ ^ 2 * l * w₁
      - 6 * W.a₂ ^ 2 * W.a₄ * z₁ ^ 2 * l * w₁ + 2 * W.a₁ * W.a₃ * W.a₄ * z₁ ^ 2 * l * w₁
      + 2 * W.a₄ ^ 2 * z₁ ^ 2 * l * w₁ - 6 * W.a₂ * W.a₆ * z₁ ^ 2 * l * w₁
      + W.a₂ * W.a₃ ^ 2 * l ^ 2 * w₁ - W.a₁ * W.a₃ * W.a₄ * l ^ 2 * w₁ - W.a₄ ^ 2 * l ^ 2 * w₁
      + W.a₁ ^ 2 * W.a₆ * l ^ 2 * w₁ + 4 * W.a₂ * W.a₆ * l ^ 2 * w₁
      - W.a₁ * W.a₂ * W.a₃ ^ 2 * z₁ * l ^ 2 * w₁ + W.a₃ ^ 3 * z₁ * l ^ 2 * w₁
      + W.a₁ ^ 2 * W.a₃ * W.a₄ * z₁ * l ^ 2 * w₁ + W.a₁ * W.a₄ ^ 2 * z₁ * l ^ 2 * w₁
      - W.a₁ ^ 3 * W.a₆ * z₁ * l ^ 2 * w₁ - 4 * W.a₁ * W.a₂ * W.a₆ * z₁ * l ^ 2 * w₁
      - 3 * W.a₃ * W.a₆ * z₁ * l ^ 2 * w₁ - 2 * W.a₂ ^ 2 * W.a₃ ^ 2 * z₁ ^ 2 * l ^ 2 * w₁
      + 2 * W.a₁ * W.a₂ * W.a₃ * W.a₄ * z₁ ^ 2 * l ^ 2 * w₁
      + 2 * W.a₂ * W.a₄ ^ 2 * z₁ ^ 2 * l ^ 2 * w₁
      - 2 * W.a₁ ^ 2 * W.a₂ * W.a₆ * z₁ ^ 2 * l ^ 2 * w₁
      - 8 * W.a₂ ^ 2 * W.a₆ * z₁ ^ 2 * l ^ 2 * w₁ + 6 * W.a₁ * W.a₃ * W.a₆ * z₁ ^ 2 * l ^ 2 * w₁
      + 6 * W.a₄ * W.a₆ * z₁ ^ 2 * l ^ 2 * w₁ - 6 * W.a₂ ^ 2 * W.a₃ * w₁ ^ 2
      - 2 * W.a₁ * W.a₃ ^ 2 * w₁ ^ 2 - 2 * W.a₃ * W.a₄ * w₁ ^ 2 + 3 * W.a₁ * W.a₆ * w₁ ^ 2
      + 4 * W.a₂ * W.a₃ ^ 2 * z₁ * w₁ ^ 2 - 6 * W.a₂ ^ 2 * W.a₄ * z₁ * w₁ ^ 2
      - 4 * W.a₁ * W.a₃ * W.a₄ * z₁ * w₁ ^ 2 - 4 * W.a₄ ^ 2 * z₁ * w₁ ^ 2
      + 12 * W.a₂ * W.a₆ * z₁ * w₁ ^ 2 + W.a₁ * W.a₂ * W.a₃ ^ 2 * l * w₁ ^ 2
      - 4 * W.a₃ ^ 3 * l * w₁ ^ 2 - W.a₁ ^ 2 * W.a₃ * W.a₄ * l * w₁ ^ 2
      - 6 * W.a₂ * W.a₃ * W.a₄ * l * w₁ ^ 2 - W.a₁ * W.a₄ ^ 2 * l * w₁ ^ 2
      + W.a₁ ^ 3 * W.a₆ * l * w₁ ^ 2 + 4 * W.a₁ * W.a₂ * W.a₆ * l * w₁ ^ 2
      - 9 * W.a₃ * W.a₆ * l * w₁ ^ 2 + W.a₂ ^ 2 * W.a₃ ^ 2 * z₁ * l * w₁ ^ 2
      - W.a₁ * W.a₂ * W.a₃ * W.a₄ * z₁ * l * w₁ ^ 2 - 7 * W.a₂ * W.a₄ ^ 2 * z₁ * l * w₁ ^ 2
      + W.a₁ ^ 2 * W.a₂ * W.a₆ * z₁ * l * w₁ ^ 2 + 4 * W.a₂ ^ 2 * W.a₆ * z₁ * l * w₁ ^ 2
      - 3 * W.a₁ * W.a₃ * W.a₆ * z₁ * l * w₁ ^ 2 - 3 * W.a₄ * W.a₆ * z₁ * l * w₁ ^ 2
      - W.a₂ * W.a₃ ^ 3 * l ^ 2 * w₁ ^ 2 + W.a₁ * W.a₃ ^ 2 * W.a₄ * l ^ 2 * w₁ ^ 2
      + W.a₃ * W.a₄ ^ 2 * l ^ 2 * w₁ ^ 2 - W.a₁ ^ 2 * W.a₃ * W.a₆ * l ^ 2 * w₁ ^ 2
      - 4 * W.a₂ * W.a₃ * W.a₆ * l ^ 2 * w₁ ^ 2 - 2 * W.a₂ * W.a₃ ^ 2 * W.a₄ * z₁ * l ^ 2 * w₁ ^ 2
      + 2 * W.a₁ * W.a₃ * W.a₄ ^ 2 * z₁ * l ^ 2 * w₁ ^ 2 + 2 * W.a₄ ^ 3 * z₁ * l ^ 2 * w₁ ^ 2
      + 6 * W.a₃ ^ 2 * W.a₆ * z₁ * l ^ 2 * w₁ ^ 2
      - 2 * W.a₁ ^ 2 * W.a₄ * W.a₆ * z₁ * l ^ 2 * w₁ ^ 2
      - 8 * W.a₂ * W.a₄ * W.a₆ * z₁ * l ^ 2 * w₁ ^ 2 + 18 * W.a₆ ^ 2 * z₁ * l ^ 2 * w₁ ^ 2
      + W.a₂ ^ 2 * W.a₃ ^ 2 * w₁ ^ 3 - W.a₁ * W.a₂ * W.a₃ * W.a₄ * w₁ ^ 3
      - W.a₂ * W.a₄ ^ 2 * w₁ ^ 3 + W.a₁ ^ 2 * W.a₂ * W.a₆ * w₁ ^ 3 - 2 * W.a₂ ^ 2 * W.a₆ * w₁ ^ 3
      - 3 * W.a₁ * W.a₃ * W.a₆ * w₁ ^ 3 - 3 * W.a₄ * W.a₆ * w₁ ^ 3
      + 2 * W.a₂ * W.a₃ ^ 2 * W.a₄ * l * w₁ ^ 3 - 2 * W.a₁ * W.a₃ * W.a₄ ^ 2 * l * w₁ ^ 3
      - 2 * W.a₄ ^ 3 * l * w₁ ^ 3 - 6 * W.a₃ ^ 2 * W.a₆ * l * w₁ ^ 3
      + 2 * W.a₁ ^ 2 * W.a₄ * W.a₆ * l * w₁ ^ 3 + 2 * W.a₂ * W.a₄ * W.a₆ * l * w₁ ^ 3
      - 18 * W.a₆ ^ 2 * l * w₁ ^ 3 + W.a₁ ^ 2 * z₂ - W.a₁ ^ 3 * z₁ * z₂
      - W.a₁ ^ 2 * W.a₂ * z₁ ^ 2 * z₂ - W.a₂ ^ 2 * z₁ ^ 2 * z₂ + 3 * W.a₁ * W.a₃ * z₁ ^ 2 * z₂
      + 3 * W.a₄ * z₁ ^ 2 * z₂ + 2 * W.a₁ * W.a₃ * l * z₂ - 2 * W.a₁ ^ 2 * W.a₃ * z₁ * l * z₂
      + 3 * W.a₃ ^ 2 * z₁ ^ 2 * l * z₂ - W.a₁ ^ 2 * W.a₄ * z₁ ^ 2 * l * z₂
      - W.a₂ * W.a₄ * z₁ ^ 2 * l * z₂ + 9 * W.a₆ * z₁ ^ 2 * l * z₂ + W.a₃ ^ 2 * l ^ 2 * z₂
      - W.a₁ * W.a₃ ^ 2 * z₁ * l ^ 2 * z₂ + W.a₂ * W.a₃ ^ 2 * z₁ ^ 2 * l ^ 2 * z₂
      - W.a₁ * W.a₃ * W.a₄ * z₁ ^ 2 * l ^ 2 * z₂ - W.a₄ ^ 2 * z₁ ^ 2 * l ^ 2 * z₂
      + 3 * W.a₂ * W.a₆ * z₁ ^ 2 * l ^ 2 * z₂ - W.a₁ ^ 2 * W.a₃ * w₁ * z₂
      + 3 * W.a₃ ^ 2 * z₁ * w₁ * z₂ - W.a₁ ^ 2 * W.a₄ * z₁ * w₁ * z₂ - W.a₂ * W.a₄ * z₁ * w₁ * z₂
      + 9 * W.a₆ * z₁ * w₁ * z₂ - 2 * W.a₁ * W.a₃ ^ 2 * l * w₁ * z₂
      + 4 * W.a₂ * W.a₃ ^ 2 * z₁ * l * w₁ * z₂ - 4 * W.a₁ * W.a₃ * W.a₄ * z₁ * l * w₁ * z₂
      - 4 * W.a₄ ^ 2 * z₁ * l * w₁ * z₂ + 12 * W.a₂ * W.a₆ * z₁ * l * w₁ * z₂
      - W.a₃ ^ 3 * l ^ 2 * w₁ * z₂ + W.a₂ ^ 2 * W.a₃ ^ 2 * z₁ * l ^ 2 * w₁ * z₂
      - W.a₁ * W.a₂ * W.a₃ * W.a₄ * z₁ * l ^ 2 * w₁ * z₂ - W.a₂ * W.a₄ ^ 2 * z₁ * l ^ 2 * w₁ * z₂
      + W.a₁ ^ 2 * W.a₂ * W.a₆ * z₁ * l ^ 2 * w₁ * z₂ + 4 * W.a₂ ^ 2 * W.a₆ * z₁ * l ^ 2 * w₁ * z₂
      - 3 * W.a₁ * W.a₃ * W.a₆ * z₁ * l ^ 2 * w₁ * z₂ - 3 * W.a₄ * W.a₆ * z₁ * l ^ 2 * w₁ * z₂
      + W.a₂ * W.a₃ ^ 2 * w₁ ^ 2 * z₂ - W.a₁ * W.a₃ * W.a₄ * w₁ ^ 2 * z₂ - W.a₄ ^ 2 * w₁ ^ 2 * z₂
      + 3 * W.a₂ * W.a₆ * w₁ ^ 2 * z₂ + W.a₂ ^ 2 * W.a₃ ^ 2 * l * w₁ ^ 2 * z₂
      - W.a₁ * W.a₂ * W.a₃ * W.a₄ * l * w₁ ^ 2 * z₂ - W.a₂ * W.a₄ ^ 2 * l * w₁ ^ 2 * z₂
      + W.a₁ ^ 2 * W.a₂ * W.a₆ * l * w₁ ^ 2 * z₂ + 4 * W.a₂ ^ 2 * W.a₆ * l * w₁ ^ 2 * z₂
      - 3 * W.a₁ * W.a₃ * W.a₆ * l * w₁ ^ 2 * z₂ - 3 * W.a₄ * W.a₆ * l * w₁ ^ 2 * z₂
      + W.a₂ * W.a₃ ^ 2 * W.a₄ * l ^ 2 * w₁ ^ 2 * z₂
      - W.a₁ * W.a₃ * W.a₄ ^ 2 * l ^ 2 * w₁ ^ 2 * z₂ - W.a₄ ^ 3 * l ^ 2 * w₁ ^ 2 * z₂
      - 3 * W.a₃ ^ 2 * W.a₆ * l ^ 2 * w₁ ^ 2 * z₂ + W.a₁ ^ 2 * W.a₄ * W.a₆ * l ^ 2 * w₁ ^ 2 * z₂
      + 4 * W.a₂ * W.a₄ * W.a₆ * l ^ 2 * w₁ ^ 2 * z₂ - 9 * W.a₆ ^ 2 * l ^ 2 * w₁ ^ 2 * z₂) * hl
end GlobalTheory.AddLaw
