-- Prove2me | solution 1 for GlobalTheory.AddLaw.diagZ_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:54:13.083161+00:00
-- url     : https://prove2.me/submissions/06b8a315-1d1d-4b97-ac29-a72992cc909b

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
theorem _root_.solution {P : Fin 3 → R} (hP : W.Equation P) : diagZ W P P = W.dblZ P := by
  linear_combination (norm := (simp only [diagZ, dblZ, negY]; ring1))
    (-3 * W.a₁ * P 0 - 6 * P 1 - 3 * W.a₃ * P 2) * (sub_eq_zero.mpr <| (equation_iff _).mp hP)
end GlobalTheory.AddLaw
