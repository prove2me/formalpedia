-- Prove2me | solution 1 for GlobalTheory.AddLaw.negDiagY_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:54:15.957897+00:00
-- url     : https://prove2.me/submissions/aa0acbef-2999-4093-a497-631b543f2709

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
theorem _root_.solution {P : Fin 3 → R} (hP : W.Equation P) : negDiagY W P P = W.negDblY P := by
  linear_combination (norm := (simp only [negDiagY, negDblY]; ring1))
    (2 * W.a₁ ^ 2 * W.a₂ * P 0 + 8 * W.a₂ ^ 2 * P 0 - 6 * W.a₁ * W.a₃ * P 0 + 3 * W.a₄ * P 0
      - W.a₁ ^ 3 * P 1 - 4 * W.a₁ * W.a₂ * P 1 - 6 * W.a₃ * P 1 - 3 * W.a₃ ^ 2 * P 2
      + W.a₁ ^ 2 * W.a₄ * P 2 + 4 * W.a₂ * W.a₄ * P 2 - 9 * W.a₆ * P 2) * (sub_eq_zero.mpr <| (equation_iff _).mp hP)
end GlobalTheory.AddLaw
