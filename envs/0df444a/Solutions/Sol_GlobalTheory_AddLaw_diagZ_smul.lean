-- Prove2me | solution 1 for GlobalTheory.AddLaw.diagZ_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:52.635628+00:00
-- url     : https://prove2.me/submissions/9c92ee29-7cdf-478e-bb47-93e963aefb03

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
theorem _root_.solution (P Q : Fin 3 → R) (u v : R) :
    diagZ W (u • P) (v • Q) = (u * v) ^ 2 * diagZ W P Q := by
  simp only [diagZ, smul_fin3_ext]
  ring1
end GlobalTheory.AddLaw
