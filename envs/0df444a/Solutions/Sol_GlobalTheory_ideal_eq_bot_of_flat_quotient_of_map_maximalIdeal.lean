-- Prove2me | solution 1 for GlobalTheory.ideal_eq_bot_of_flat_quotient_of_map_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:38:36.148017+00:00
-- url     : https://prove2.me/submissions/f175945a-4f7a-4b75-adf0-13ad8f747daa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_ideal_eq_bot_of_flat_quotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open IsLocalRing
namespace GlobalTheory
theorem _root_.solution (T : Type*) {R : Type*} [CommRing T]
    [IsDomain T] [IsDiscreteValuationRing T] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra T R] (h : (maximalIdeal T).map (algebraMap T R) = maximalIdeal R) {J : Ideal R}
    (hJ : J ≠ ⊤) [Module.Flat T (R ⧸ J)] : J = ⊥ :=
  haveI : IsLocalHom (algebraMap T R) := ((local_hom_TFAE (algebraMap T R)).out 0 2).mpr h.le
  ideal_eq_bot_of_flat_quotient T hJ
end GlobalTheory
