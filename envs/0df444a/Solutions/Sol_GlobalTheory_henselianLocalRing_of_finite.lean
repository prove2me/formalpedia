-- Prove2me | solution 1 for GlobalTheory.henselianLocalRing_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:45:28.727266+00:00
-- url     : https://prove2.me/submissions/1d17e989-4c50-4db2-a265-8c8130a8c021

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Theorems.Thm_GlobalTheory_henselianRing_of_finite
import Theorems.Thm_GlobalTheory_henselianLocalRing_of_henselianRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct
namespace GlobalTheory
theorem _root_.solution (R S : Type*) [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S] [IsLocalRing S] :
    HenselianLocalRing S :=
  have := henselianRing_of_finite R (maximalIdeal S)
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  henselianLocalRing_of_henselianRing S
end GlobalTheory
