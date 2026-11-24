-- Prove2me | solution 1 for GlobalTheory.isLocalHom_of_comp_algebraMap_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:04:53.935207+00:00
-- url     : https://prove2.me/submissions/42c9e422-d5a6-416d-978f-26a5593a95c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution {A B : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsLocalRing B] (f : A →+* B) [IsLocalHom f]
    (g : AdicCompletion (IsLocalRing.maximalIdeal A) A →+* B) (hg : g.comp (algebraMap A _) = f) :
    IsLocalHom g := by
  refine ((IsLocalRing.local_hom_TFAE g).out 0 2).2 ?_
  rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, hg]
  exact ((IsLocalRing.local_hom_TFAE f).out 0 2).1 ‹_›
end GlobalTheory
