-- Prove2me | solution 1 for GlobalTheory.AddLaw.diagX_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:54:12.134882+00:00
-- url     : https://prove2.me/submissions/f03d2aeb-c1ad-49b2-846e-066327286299

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
theorem _root_.solution {P : Fin 3 → R} (hP : W.Equation P) : diagX W P P = W.dblX P := by
  linear_combination (norm := (simp only [diagX, dblX]; ring1))
    (W.a₁ ^ 3 * P 0 + 4 * W.a₁ * W.a₂ * P 0 + 9 * W.a₃ * P 0 + 2 * W.a₁ ^ 2 * P 1
      + 8 * W.a₂ * P 1 + W.a₁ ^ 2 * W.a₃ * P 2 + 4 * W.a₂ * W.a₃ * P 2) * (sub_eq_zero.mpr <| (equation_iff _).mp hP)
end GlobalTheory.AddLaw
