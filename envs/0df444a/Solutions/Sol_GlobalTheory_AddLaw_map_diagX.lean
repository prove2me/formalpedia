-- Prove2me | solution 1 for GlobalTheory.AddLaw.map_diagX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:52.837648+00:00
-- url     : https://prove2.me/submissions/b86cdf9c-4fac-49c6-8b79-6d6e62a91f3c

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
    diagX (W.map f) (f ∘ P) (f ∘ Q) = f (diagX W P Q) := by
  simp only [diagX, map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow,
    WeierstrassCurve.map, Function.comp_apply]
end GlobalTheory.AddLaw
