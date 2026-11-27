-- Prove2me | solution 1 for GlobalTheory.isDiscreteValuationRing_localization_of_isDedekindDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:38:47.08689+00:00
-- url     : https://prove2.me/submissions/10098198-e2d8-48e7-8015-bc964f5b1f6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsDiscreteValuationRingLocalizationOfIsDedekindD
import Theorems.Thm_GlobalTheory_NormVal_liesOver_maximalIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsDiscreteValuationRing IsLocalRing Module TensorProduct
open NormVal
variable (R : Type*) {S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S]
include R
namespace GlobalTheory
theorem _root_.solution [IsDedekindDomain S]
    (n : MaximalSpectrum S) : IsDiscreteValuationRing (Localization.AtPrime n.asIdeal) := by
  have := liesOver_maximalIdeal R n.asIdeal
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S
    (Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field R) n.asIdeal) _
end GlobalTheory
