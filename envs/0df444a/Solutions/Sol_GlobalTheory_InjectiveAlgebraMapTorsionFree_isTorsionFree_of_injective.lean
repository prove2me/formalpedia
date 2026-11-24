-- Prove2me | solution 1 for GlobalTheory.InjectiveAlgebraMapTorsionFree.isTorsionFree_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:47:58.088991+00:00
-- url     : https://prove2.me/submissions/5e4cda16-4a31-4f8a-9ce5-59d6427dcb87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInjectiveNormLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.InjectiveAlgebraMapTorsionFree
variable (p : ℕ) [Fact (Nat.Prime p)]
namespace GlobalTheory.InjectiveAlgebraMapTorsionFree
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] [IsDomain R]
    [IsDomain S] [Algebra R S] (h : Function.Injective (algebraMap R S)) :
    Module.IsTorsionFree R S :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr h
end GlobalTheory.InjectiveAlgebraMapTorsionFree
