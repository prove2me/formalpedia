-- Prove2me | solution 1 for GlobalTheory.comap_eq_maximalIdeal_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:27:41.304271+00:00
-- url     : https://prove2.me/submissions/872bb88b-15da-4643-b946-2afa2cae76b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing

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
theorem _root_.solution {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S] (n : Ideal S) [n.IsMaximal] :
    n.comap (algebraMap R S) = maximalIdeal R :=
  IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n)
end GlobalTheory
