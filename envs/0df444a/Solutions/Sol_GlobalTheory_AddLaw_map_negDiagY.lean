-- Prove2me | solution 1 for GlobalTheory.AddLaw.map_negDiagY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:54:14.020979+00:00
-- url     : https://prove2.me/submissions/82a48bcc-5db3-4096-9541-923e3a5193ad

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
theorem _root_.solution (f : R →+* S) (P Q : Fin 3 → R) :
    negDiagY (W.map f) (f ∘ P) (f ∘ Q) = f (negDiagY W P Q) := by
  simp only [negDiagY, map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow,
    WeierstrassCurve.map, Function.comp_apply]
end GlobalTheory.AddLaw
