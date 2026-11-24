-- Prove2me | solution 1 for GlobalTheory.addVal_algebraMap_uniformizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:21:19.815153+00:00
-- url     : https://prove2.me/submissions/cef71182-82bc-4998-aea5-fd9e0b4cd49b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthBaseChangeQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_length_quotient_span_singleton_eq_addVal
import Theorems.Thm_GlobalTheory_length_fibre_eq_ramificationIdx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
open IsDiscreteValuationRing hiding maximalIdeal
variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [IsDiscreteValuationRing R] [IsDiscreteValuationRing S] [Algebra R S] [FaithfulSMul R S]
variable [IsLocalHom (algebraMap R S)]
variable {R}
namespace GlobalTheory
theorem _root_.solution {ϖ : R} (hϖ : Irreducible ϖ) :
    addVal S (algebraMap R S ϖ) = ((maximalIdeal S).ramificationIdx R : ℕ) := by
  rw [← length_fibre_eq_ramificationIdx, ← length_quotient_span_singleton_eq_addVal,
    hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
end GlobalTheory
