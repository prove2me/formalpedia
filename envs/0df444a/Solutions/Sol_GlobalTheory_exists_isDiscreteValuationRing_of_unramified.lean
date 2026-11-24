-- Prove2me | solution 1 for GlobalTheory.exists_isDiscreteValuationRing_of_unramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:00:06.717853+00:00
-- url     : https://prove2.me/submissions/6d0eeb3e-ea6d-403c-9e76-56f8d1b0d86f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Theorems.Thm_GlobalTheory_exists_isDiscreteValuationRing_of_flat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
open scoped TensorProduct
variable (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
namespace GlobalTheory
theorem _root_.solution (B : Type*) [CommRing B] [IsLocalRing B]
    [Algebra V B] [IsLocalHom (algebraMap V B)] [Module.Flat V B] [Algebra.EssFiniteType V B]
    [Algebra.FormallyUnramified V B] : ∃ _ : IsDomain B, IsDiscreteValuationRing B := by
  have : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing V B
  exact exists_isDiscreteValuationRing_of_flat V B Algebra.FormallyUnramified.map_maximalIdeal
    (Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal B).ne_top)
end GlobalTheory
