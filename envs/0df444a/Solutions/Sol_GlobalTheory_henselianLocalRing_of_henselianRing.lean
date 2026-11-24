-- Prove2me | solution 1 for GlobalTheory.henselianLocalRing_of_henselianRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:27:42.195781+00:00
-- url     : https://prove2.me/submissions/48f19554-7077-4073-bda6-06ba5fab0741

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
theorem _root_.solution (S : Type*) [CommRing S] [IsLocalRing S]
    [HenselianRing S (maximalIdeal S)] : HenselianLocalRing S where
  is_henselian f hf a₀ h₁ h₂ := HenselianRing.is_henselian f hf a₀ h₁ (h₂.map _)
end GlobalTheory
