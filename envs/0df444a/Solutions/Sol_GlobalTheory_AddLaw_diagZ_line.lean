-- Prove2me | solution 1 for GlobalTheory.AddLaw.diagZ_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:13:36.533893+00:00
-- url     : https://prove2.me/submissions/250266a2-7a6f-4587-a967-ba7bd6e19e9b

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
    diagZ W ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)] =
      l * diagX W ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)]
      - (w₁ - l * z₁) * negDiagY W ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)] := by
  have h := sub_eq_zero.mpr <| (equation_iff _).mp h₁
  linear_combination (norm := (simp only [originN, originD, diagX, diagZ, negDiagY, fin3_def_ext]; ring1))
    (-3 + 3 * W.a₁ * z₁ + 3 * W.a₂ * z₁ ^ 2 - W.a₁ ^ 2 * l - 4 * W.a₂ * l
      - W.a₁ ^ 2 * W.a₃ * z₁ * l ^ 2 - 4 * W.a₂ * W.a₃ * z₁ * l ^ 2
      - W.a₂ * W.a₃ ^ 2 * z₁ ^ 2 * l ^ 3 + W.a₁ * W.a₃ * W.a₄ * z₁ ^ 2 * l ^ 3
      + W.a₄ ^ 2 * z₁ ^ 2 * l ^ 3 + W.a₁ ^ 3 * w₁ + 4 * W.a₁ * W.a₂ * w₁ + 3 * W.a₃ * w₁
      + W.a₁ ^ 2 * W.a₂ * z₁ * w₁ + 4 * W.a₂ ^ 2 * z₁ * w₁ - 3 * W.a₁ * W.a₃ * z₁ * w₁
      - 3 * W.a₄ * z₁ * w₁ + 2 * W.a₁ ^ 2 * W.a₃ * l * w₁ + 8 * W.a₂ * W.a₃ * l * w₁
      + 3 * W.a₂ * W.a₃ ^ 2 * z₁ * l ^ 2 * w₁ - 3 * W.a₁ * W.a₃ * W.a₄ * z₁ * l ^ 2 * w₁
      - 3 * W.a₄ ^ 2 * z₁ * l ^ 2 * w₁ - 3 * W.a₃ ^ 2 * w₁ ^ 2 + W.a₁ ^ 2 * W.a₄ * w₁ ^ 2
      + 4 * W.a₂ * W.a₄ * w₁ ^ 2 - 9 * W.a₆ * w₁ ^ 2 - 3 * W.a₂ * W.a₃ ^ 2 * l * w₁ ^ 2
      + 3 * W.a₁ * W.a₃ * W.a₄ * l * w₁ ^ 2 + 3 * W.a₄ ^ 2 * l * w₁ ^ 2 + 3 * W.a₁ * z₂
      + 3 * W.a₂ * z₁ * z₂ + W.a₁ ^ 3 * l * z₂ + 4 * W.a₁ * W.a₂ * l * z₂ + 3 * W.a₃ * l * z₂
      + W.a₁ ^ 2 * W.a₃ * l ^ 2 * z₂ + 4 * W.a₂ * W.a₃ * l ^ 2 * z₂
      + 3 * W.a₃ ^ 2 * z₁ * l ^ 2 * z₂ - W.a₁ ^ 2 * W.a₄ * z₁ * l ^ 2 * z₂
      - 4 * W.a₂ * W.a₄ * z₁ * l ^ 2 * z₂ + 9 * W.a₆ * z₁ * l ^ 2 * z₂
      + 2 * W.a₂ * W.a₃ ^ 2 * z₁ * l ^ 3 * z₂ - 2 * W.a₁ * W.a₃ * W.a₄ * z₁ * l ^ 3 * z₂
      - 2 * W.a₄ ^ 2 * z₁ * l ^ 3 * z₂ + W.a₁ ^ 2 * W.a₂ * w₁ * z₂ + 4 * W.a₂ ^ 2 * w₁ * z₂
      - 3 * W.a₁ * W.a₃ * w₁ * z₂ - 3 * W.a₄ * w₁ * z₂ - 6 * W.a₃ ^ 2 * l * w₁ * z₂
      + 2 * W.a₁ ^ 2 * W.a₄ * l * w₁ * z₂ + 8 * W.a₂ * W.a₄ * l * w₁ * z₂
      - 18 * W.a₆ * l * w₁ * z₂ - 3 * W.a₂ * W.a₃ ^ 2 * l ^ 2 * w₁ * z₂
      + 3 * W.a₁ * W.a₃ * W.a₄ * l ^ 2 * w₁ * z₂ + 3 * W.a₄ ^ 2 * l ^ 2 * w₁ * z₂
      + 3 * W.a₂ * z₂ ^ 2 + W.a₁ ^ 2 * W.a₂ * l * z₂ ^ 2 + 4 * W.a₂ ^ 2 * l * z₂ ^ 2
      - 3 * W.a₁ * W.a₃ * l * z₂ ^ 2 - 3 * W.a₄ * l * z₂ ^ 2 - 3 * W.a₃ ^ 2 * l ^ 2 * z₂ ^ 2
      + W.a₁ ^ 2 * W.a₄ * l ^ 2 * z₂ ^ 2 + 4 * W.a₂ * W.a₄ * l ^ 2 * z₂ ^ 2
      - 9 * W.a₆ * l ^ 2 * z₂ ^ 2 - W.a₂ * W.a₃ ^ 2 * l ^ 3 * z₂ ^ 2
      + W.a₁ * W.a₃ * W.a₄ * l ^ 3 * z₂ ^ 2 + W.a₄ ^ 2 * l ^ 3 * z₂ ^ 2) * h
    + (-3 * z₁ + 3 * W.a₁ * z₁ ^ 2 + 3 * W.a₂ * z₁ ^ 3 - W.a₁ ^ 2 * w₁ - 4 * W.a₂ * w₁
      + W.a₁ ^ 3 * z₁ * w₁ + 4 * W.a₁ * W.a₂ * z₁ * w₁ + 3 * W.a₃ * z₁ * w₁
      + W.a₁ ^ 2 * W.a₂ * z₁ ^ 2 * w₁ + 4 * W.a₂ ^ 2 * z₁ ^ 2 * w₁ - 3 * W.a₁ * W.a₃ * z₁ ^ 2 * w₁
      - 3 * W.a₄ * z₁ ^ 2 * w₁ + W.a₁ ^ 2 * W.a₃ * w₁ ^ 2 + 4 * W.a₂ * W.a₃ * w₁ ^ 2
      - 3 * W.a₃ ^ 2 * z₁ * w₁ ^ 2 + W.a₁ ^ 2 * W.a₄ * z₁ * w₁ ^ 2 + 4 * W.a₂ * W.a₄ * z₁ * w₁ ^ 2
      - 9 * W.a₆ * z₁ * w₁ ^ 2 - W.a₂ * W.a₃ ^ 2 * w₁ ^ 3 + W.a₁ * W.a₃ * W.a₄ * w₁ ^ 3
      + W.a₄ ^ 2 * w₁ ^ 3) * hl
end GlobalTheory.AddLaw
