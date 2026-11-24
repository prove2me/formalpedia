-- Prove2me | solution 1 for GlobalTheory.AddLaw.diagX_mul_addZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:54:10.0434+00:00
-- url     : https://prove2.me/submissions/ea82dae4-48e4-4e20-bd20-c80bdf04e0cd

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
theorem _root_.solution {P Q : Fin 3 → R} (hP : W.Equation P) (hQ : W.Equation Q) :
    diagX W P Q * W.addZ P Q = diagZ W P Q * W.addX P Q := by
  linear_combination (norm := (simp only [diagX, diagZ, addZ, addX]; ring1))
    (-3 * W.a₁ * P 2 * Q 0 ^ 2 * Q 1 ^ 2 - 3 * P 2 * Q 0 * Q 1 ^ 3
      + 3 * W.a₁ ^ 2 * P 1 * Q 0 ^ 3 * Q 2 - W.a₁ ^ 3 * W.a₂ * P 2 * Q 0 ^ 3 * Q 2
      - W.a₁ * W.a₂ ^ 2 * P 2 * Q 0 ^ 3 * Q 2 + 3 * W.a₁ ^ 2 * W.a₃ * P 2 * Q 0 ^ 3 * Q 2
      + 3 * W.a₁ * W.a₄ * P 2 * Q 0 ^ 3 * Q 2 - 3 * W.a₁ ^ 2 * P 0 * Q 0 ^ 2 * Q 1 * Q 2
      - 3 * W.a₁ * P 1 * Q 0 ^ 2 * Q 1 * Q 2 + W.a₁ ^ 2 * W.a₂ * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      + W.a₂ ^ 2 * P 2 * Q 0 ^ 2 * Q 1 * Q 2 - 6 * W.a₁ * W.a₃ * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      - 3 * W.a₄ * P 2 * Q 0 ^ 2 * Q 1 * Q 2 - 3 * W.a₁ * P 0 * Q 0 * Q 1 ^ 2 * Q 2
      - 3 * P 1 * Q 0 * Q 1 ^ 2 * Q 2 - W.a₁ ^ 3 * P 2 * Q 0 * Q 1 ^ 2 * Q 2
      - W.a₁ * W.a₂ * P 2 * Q 0 * Q 1 ^ 2 * Q 2 - 6 * W.a₃ * P 2 * Q 0 * Q 1 ^ 2 * Q 2
      - W.a₁ ^ 2 * P 2 * Q 1 ^ 3 * Q 2 - W.a₂ * P 2 * Q 1 ^ 3 * Q 2
      + W.a₁ ^ 3 * W.a₂ * P 0 * Q 0 ^ 2 * Q 2 ^ 2 + W.a₁ * W.a₂ ^ 2 * P 0 * Q 0 ^ 2 * Q 2 ^ 2
      - 3 * W.a₁ ^ 2 * W.a₃ * P 0 * Q 0 ^ 2 * Q 2 ^ 2 - 3 * W.a₁ * W.a₄ * P 0 * Q 0 ^ 2 * Q 2 ^ 2
      + 4 * W.a₁ ^ 2 * W.a₂ * P 1 * Q 0 ^ 2 * Q 2 ^ 2 + W.a₂ ^ 2 * P 1 * Q 0 ^ 2 * Q 2 ^ 2
      - 3 * W.a₁ * W.a₃ * P 1 * Q 0 ^ 2 * Q 2 ^ 2 - 3 * W.a₄ * P 1 * Q 0 ^ 2 * Q 2 ^ 2
      - W.a₁ ^ 3 * W.a₂ ^ 2 * P 2 * Q 0 ^ 2 * Q 2 ^ 2 - W.a₁ * W.a₂ ^ 3 * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      + 4 * W.a₁ ^ 2 * W.a₂ * W.a₃ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      + W.a₂ ^ 2 * W.a₃ * P 2 * Q 0 ^ 2 * Q 2 ^ 2 - 3 * W.a₁ * W.a₃ ^ 2 * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      + 3 * W.a₁ * W.a₂ * W.a₄ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      - 3 * W.a₃ * W.a₄ * P 2 * Q 0 ^ 2 * Q 2 ^ 2 - W.a₁ ^ 4 * P 0 * Q 0 * Q 1 * Q 2 ^ 2
      - W.a₁ ^ 2 * W.a₂ * P 0 * Q 0 * Q 1 * Q 2 ^ 2 - 3 * W.a₁ * W.a₃ * P 0 * Q 0 * Q 1 * Q 2 ^ 2
      - 4 * W.a₁ ^ 3 * P 1 * Q 0 * Q 1 * Q 2 ^ 2 - W.a₁ * W.a₂ * P 1 * Q 0 * Q 1 * Q 2 ^ 2
      - 3 * W.a₃ * P 1 * Q 0 * Q 1 * Q 2 ^ 2 + W.a₁ ^ 4 * W.a₂ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      + W.a₁ ^ 2 * W.a₂ ^ 2 * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 4 * W.a₁ ^ 3 * W.a₃ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - W.a₁ * W.a₂ * W.a₃ * P 2 * Q 0 * Q 1 * Q 2 ^ 2 - 6 * W.a₃ ^ 2 * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 2 * W.a₁ ^ 2 * W.a₄ * P 2 * Q 0 * Q 1 * Q 2 ^ 2 + W.a₂ * W.a₄ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 9 * W.a₆ * P 2 * Q 0 * Q 1 * Q 2 ^ 2 - W.a₁ ^ 3 * P 0 * Q 1 ^ 2 * Q 2 ^ 2
      - W.a₁ * W.a₂ * P 0 * Q 1 ^ 2 * Q 2 ^ 2 - 4 * W.a₁ ^ 2 * P 1 * Q 1 ^ 2 * Q 2 ^ 2
      - W.a₂ * P 1 * Q 1 ^ 2 * Q 2 ^ 2 + W.a₁ ^ 3 * W.a₂ * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      + W.a₁ * W.a₂ ^ 2 * P 2 * Q 1 ^ 2 * Q 2 ^ 2 - 5 * W.a₁ ^ 2 * W.a₃ * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      - 2 * W.a₂ * W.a₃ * P 2 * Q 1 ^ 2 * Q 2 ^ 2 - 3 * W.a₁ * W.a₄ * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      - 3 * W.a₁ * W.a₃ ^ 2 * P 0 * Q 0 * Q 2 ^ 3 + W.a₁ ^ 3 * W.a₄ * P 0 * Q 0 * Q 2 ^ 3
      + W.a₁ * W.a₂ * W.a₄ * P 0 * Q 0 * Q 2 ^ 3 - 9 * W.a₁ * W.a₆ * P 0 * Q 0 * Q 2 ^ 3
      - 3 * W.a₃ ^ 2 * P 1 * Q 0 * Q 2 ^ 3 + 4 * W.a₁ ^ 2 * W.a₄ * P 1 * Q 0 * Q 2 ^ 3
      + W.a₂ * W.a₄ * P 1 * Q 0 * Q 2 ^ 3 - 9 * W.a₆ * P 1 * Q 0 * Q 2 ^ 3
      - 3 * W.a₃ ^ 3 * P 2 * Q 0 * Q 2 ^ 3 - W.a₁ ^ 3 * W.a₂ * W.a₄ * P 2 * Q 0 * Q 2 ^ 3
      - W.a₁ * W.a₂ ^ 2 * W.a₄ * P 2 * Q 0 * Q 2 ^ 3
      + 4 * W.a₁ ^ 2 * W.a₃ * W.a₄ * P 2 * Q 0 * Q 2 ^ 3
      + W.a₂ * W.a₃ * W.a₄ * P 2 * Q 0 * Q 2 ^ 3 + 3 * W.a₁ * W.a₄ ^ 2 * P 2 * Q 0 * Q 2 ^ 3
      - 9 * W.a₃ * W.a₆ * P 2 * Q 0 * Q 2 ^ 3 - W.a₁ ^ 3 * W.a₃ * P 0 * Q 1 * Q 2 ^ 3
      - W.a₁ * W.a₂ * W.a₃ * P 0 * Q 1 * Q 2 ^ 3 - 4 * W.a₁ ^ 2 * W.a₃ * P 1 * Q 1 * Q 2 ^ 3
      - W.a₂ * W.a₃ * P 1 * Q 1 * Q 2 ^ 3 + W.a₁ ^ 3 * W.a₂ * W.a₃ * P 2 * Q 1 * Q 2 ^ 3
      + W.a₁ * W.a₂ ^ 2 * W.a₃ * P 2 * Q 1 * Q 2 ^ 3
      - 4 * W.a₁ ^ 2 * W.a₃ ^ 2 * P 2 * Q 1 * Q 2 ^ 3 - 2 * W.a₂ * W.a₃ ^ 2 * P 2 * Q 1 * Q 2 ^ 3
      - 2 * W.a₁ * W.a₃ * W.a₄ * P 2 * Q 1 * Q 2 ^ 3 + W.a₄ ^ 2 * P 2 * Q 1 * Q 2 ^ 3
      - 3 * W.a₂ * W.a₆ * P 2 * Q 1 * Q 2 ^ 3 - W.a₁ * W.a₂ * W.a₃ ^ 2 * P 0 * Q 2 ^ 4
      + W.a₁ ^ 2 * W.a₃ * W.a₄ * P 0 * Q 2 ^ 4 + W.a₁ * W.a₄ ^ 2 * P 0 * Q 2 ^ 4
      - 3 * W.a₁ * W.a₂ * W.a₆ * P 0 * Q 2 ^ 4 - W.a₂ * W.a₃ ^ 2 * P 1 * Q 2 ^ 4
      + W.a₁ * W.a₃ * W.a₄ * P 1 * Q 2 ^ 4 + W.a₄ ^ 2 * P 1 * Q 2 ^ 4
      + 3 * W.a₁ ^ 2 * W.a₆ * P 1 * Q 2 ^ 4 - 3 * W.a₂ * W.a₆ * P 1 * Q 2 ^ 4
      - W.a₂ * W.a₃ ^ 3 * P 2 * Q 2 ^ 4 + W.a₁ * W.a₃ ^ 2 * W.a₄ * P 2 * Q 2 ^ 4
      + W.a₃ * W.a₄ ^ 2 * P 2 * Q 2 ^ 4 - W.a₁ ^ 3 * W.a₂ * W.a₆ * P 2 * Q 2 ^ 4
      - W.a₁ * W.a₂ ^ 2 * W.a₆ * P 2 * Q 2 ^ 4 + 3 * W.a₁ ^ 2 * W.a₃ * W.a₆ * P 2 * Q 2 ^ 4
      - 3 * W.a₂ * W.a₃ * W.a₆ * P 2 * Q 2 ^ 4 + 3 * W.a₁ * W.a₄ * W.a₆ * P 2 * Q 2 ^ 4) * (sub_eq_zero.mpr <| (equation_iff _).mp hP)
    + (3 * W.a₁ * P 0 ^ 2 * P 1 * P 2 * Q 1 + 3 * P 0 * P 1 ^ 2 * P 2 * Q 1
      - W.a₁ ^ 2 * W.a₂ * P 0 ^ 2 * P 2 ^ 2 * Q 1 - W.a₂ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 1
      + 3 * W.a₁ * W.a₃ * P 0 ^ 2 * P 2 ^ 2 * Q 1 + 3 * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 1
      + W.a₁ ^ 3 * P 0 * P 1 * P 2 ^ 2 * Q 1 + W.a₁ * W.a₂ * P 0 * P 1 * P 2 ^ 2 * Q 1
      + 3 * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 1 + W.a₁ ^ 2 * P 1 ^ 2 * P 2 ^ 2 * Q 1
      + W.a₂ * P 1 ^ 2 * P 2 ^ 2 * Q 1 + 3 * W.a₃ ^ 2 * P 0 * P 2 ^ 3 * Q 1
      - W.a₁ ^ 2 * W.a₄ * P 0 * P 2 ^ 3 * Q 1 - W.a₂ * W.a₄ * P 0 * P 2 ^ 3 * Q 1
      + 9 * W.a₆ * P 0 * P 2 ^ 3 * Q 1 + W.a₁ ^ 2 * W.a₃ * P 1 * P 2 ^ 3 * Q 1
      + W.a₂ * W.a₃ * P 1 * P 2 ^ 3 * Q 1 + W.a₂ * W.a₃ ^ 2 * P 2 ^ 4 * Q 1
      - W.a₁ * W.a₃ * W.a₄ * P 2 ^ 4 * Q 1 - W.a₄ ^ 2 * P 2 ^ 4 * Q 1
      + 3 * W.a₂ * W.a₆ * P 2 ^ 4 * Q 1 + 6 * W.a₁ * P 0 ^ 2 * P 1 ^ 2 * Q 2
      + 3 * P 0 * P 1 ^ 3 * Q 2 + W.a₁ ^ 4 * P 0 ^ 2 * P 1 * P 2 * Q 2
      - 3 * W.a₁ ^ 2 * W.a₂ * P 0 ^ 2 * P 1 * P 2 * Q 2 - W.a₂ ^ 2 * P 0 ^ 2 * P 1 * P 2 * Q 2
      + 9 * W.a₁ * W.a₃ * P 0 ^ 2 * P 1 * P 2 * Q 2 + 3 * W.a₄ * P 0 ^ 2 * P 1 * P 2 * Q 2
      + 5 * W.a₁ ^ 3 * P 0 * P 1 ^ 2 * P 2 * Q 2 + 2 * W.a₁ * W.a₂ * P 0 * P 1 ^ 2 * P 2 * Q 2
      + 6 * W.a₃ * P 0 * P 1 ^ 2 * P 2 * Q 2 + 4 * W.a₁ ^ 2 * P 1 ^ 3 * P 2 * Q 2
      + W.a₂ * P 1 ^ 3 * P 2 * Q 2 + W.a₁ ^ 3 * W.a₂ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 2
      + W.a₁ * W.a₂ ^ 3 * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - 4 * W.a₁ ^ 2 * W.a₂ * W.a₃ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - W.a₂ ^ 2 * W.a₃ * P 0 ^ 2 * P 2 ^ 2 * Q 2 + 6 * W.a₁ * W.a₃ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - W.a₁ ^ 3 * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - 4 * W.a₁ * W.a₂ * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      + 3 * W.a₃ * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 2 + 9 * W.a₁ * W.a₆ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - W.a₁ ^ 4 * W.a₂ * P 0 * P 1 * P 2 ^ 2 * Q 2
      - W.a₁ ^ 2 * W.a₂ ^ 2 * P 0 * P 1 * P 2 ^ 2 * Q 2
      + 5 * W.a₁ ^ 3 * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 2
      + 2 * W.a₁ * W.a₂ * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 2
      + 6 * W.a₃ ^ 2 * P 0 * P 1 * P 2 ^ 2 * Q 2 - W.a₁ ^ 2 * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 2
      - W.a₂ * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 2 + 9 * W.a₆ * P 0 * P 1 * P 2 ^ 2 * Q 2
      - W.a₁ ^ 3 * W.a₂ * P 1 ^ 2 * P 2 ^ 2 * Q 2 - W.a₁ * W.a₂ ^ 2 * P 1 ^ 2 * P 2 ^ 2 * Q 2
      + 8 * W.a₁ ^ 2 * W.a₃ * P 1 ^ 2 * P 2 ^ 2 * Q 2 + 2 * W.a₂ * W.a₃ * P 1 ^ 2 * P 2 ^ 2 * Q 2
      + 3 * W.a₁ * W.a₄ * P 1 ^ 2 * P 2 ^ 2 * Q 2 + W.a₁ * W.a₂ * W.a₃ ^ 2 * P 0 * P 2 ^ 3 * Q 2
      + 3 * W.a₃ ^ 3 * P 0 * P 2 ^ 3 * Q 2 + W.a₁ ^ 3 * W.a₂ * W.a₄ * P 0 * P 2 ^ 3 * Q 2
      + W.a₁ * W.a₂ ^ 2 * W.a₄ * P 0 * P 2 ^ 3 * Q 2
      - 5 * W.a₁ ^ 2 * W.a₃ * W.a₄ * P 0 * P 2 ^ 3 * Q 2
      - W.a₂ * W.a₃ * W.a₄ * P 0 * P 2 ^ 3 * Q 2 - 4 * W.a₁ * W.a₄ ^ 2 * P 0 * P 2 ^ 3 * Q 2
      + 3 * W.a₁ * W.a₂ * W.a₆ * P 0 * P 2 ^ 3 * Q 2 + 9 * W.a₃ * W.a₆ * P 0 * P 2 ^ 3 * Q 2
      - W.a₁ ^ 3 * W.a₂ * W.a₃ * P 1 * P 2 ^ 3 * Q 2
      - W.a₁ * W.a₂ ^ 2 * W.a₃ * P 1 * P 2 ^ 3 * Q 2
      + 4 * W.a₁ ^ 2 * W.a₃ ^ 2 * P 1 * P 2 ^ 3 * Q 2 + 2 * W.a₂ * W.a₃ ^ 2 * P 1 * P 2 ^ 3 * Q 2
      + 2 * W.a₁ * W.a₃ * W.a₄ * P 1 * P 2 ^ 3 * Q 2 - W.a₄ ^ 2 * P 1 * P 2 ^ 3 * Q 2
      - 3 * W.a₁ ^ 2 * W.a₆ * P 1 * P 2 ^ 3 * Q 2 + 3 * W.a₂ * W.a₆ * P 1 * P 2 ^ 3 * Q 2
      + W.a₂ * W.a₃ ^ 3 * P 2 ^ 4 * Q 2 - W.a₁ * W.a₃ ^ 2 * W.a₄ * P 2 ^ 4 * Q 2
      - W.a₃ * W.a₄ ^ 2 * P 2 ^ 4 * Q 2 + W.a₁ ^ 3 * W.a₂ * W.a₆ * P 2 ^ 4 * Q 2
      + W.a₁ * W.a₂ ^ 2 * W.a₆ * P 2 ^ 4 * Q 2 - 3 * W.a₁ ^ 2 * W.a₃ * W.a₆ * P 2 ^ 4 * Q 2
      + 3 * W.a₂ * W.a₃ * W.a₆ * P 2 ^ 4 * Q 2 - 3 * W.a₁ * W.a₄ * W.a₆ * P 2 ^ 4 * Q 2) * (sub_eq_zero.mpr <| (equation_iff _).mp hQ)
end GlobalTheory.AddLaw
