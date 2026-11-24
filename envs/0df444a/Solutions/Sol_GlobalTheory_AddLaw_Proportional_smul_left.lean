-- Prove2me | solution 1 for GlobalTheory.AddLaw.Proportional.smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:54:06.652916+00:00
-- url     : https://prove2.me/submissions/37ffd8c1-38f0-4794-8932-62beaf54854f

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
theorem _root_.solution {T U : Fin 3 → R} (h : Proportional T U) (u : R) :
    Proportional (u • T) U :=
  fun i j => by simp only [Pi.smul_apply, smul_eq_mul]; linear_combination u * h i j
end Proportional
end GlobalTheory.AddLaw
