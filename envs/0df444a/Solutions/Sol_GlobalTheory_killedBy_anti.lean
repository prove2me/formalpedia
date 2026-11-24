-- Prove2me | solution 1 for GlobalTheory.killedBy_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:13:23.001416+00:00
-- url     : https://prove2.me/submissions/2948c8e8-2aef-4601-8910-773babbce8c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionCountLogConcavePrimePowers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R : Type} [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    {I J : Ideal R} (h : I ≤ J) : killedBy M J ≤ killedBy M I :=
  fun _ hx a ha => hx a (h ha)
end GlobalTheory
