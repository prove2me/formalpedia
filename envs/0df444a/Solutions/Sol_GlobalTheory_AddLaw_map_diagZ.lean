-- Prove2me | solution 1 for GlobalTheory.AddLaw.map_diagZ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:53.306998+00:00
-- url     : https://prove2.me/submissions/83a2593e-a89a-46c9-a457-3322ea1a2538

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
    diagZ (W.map f) (f ∘ P) (f ∘ Q) = f (diagZ W P Q) := by
  simp only [diagZ, map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow,
    WeierstrassCurve.map, Function.comp_apply]
end GlobalTheory.AddLaw
