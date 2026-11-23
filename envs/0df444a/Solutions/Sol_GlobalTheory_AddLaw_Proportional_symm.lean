-- Prove2me | solution 1 for GlobalTheory.AddLaw.Proportional.symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:38.317975+00:00
-- url     : https://prove2.me/submissions/b3e14e93-cecd-44f9-b4f2-27457656e923

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SubMulOriginD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero

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
namespace GlobalTheory.AddLaw
namespace Proportional
theorem _root_.solution {T U : Fin 3 → R} (h : Proportional T U) : Proportional U T :=
  fun i j => by linear_combination h j i
end Proportional
end GlobalTheory.AddLaw
