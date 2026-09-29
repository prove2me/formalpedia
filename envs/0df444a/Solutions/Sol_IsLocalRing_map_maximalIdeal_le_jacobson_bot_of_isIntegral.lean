-- Prove2me | solution 1 for IsLocalRing.map_maximalIdeal_le_jacobson_bot_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/5fed8348-e173-51cc-bdf6-263dbd98d781

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_map_maximalIdeal_le_jacobson_bot_of_isIntegral

open IsLocalRing

theorem solution {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [Algebra.IsIntegral R S] :
    (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤ Ideal.jacobson (⊥ : Ideal S) := by
  refine le_sInf fun M ⟨_, hM⟩ ↦ Ideal.map_le_iff_le_comap.mpr ?_
  haveI : M.IsMaximal := hM
  haveI : (M.comap (algebraMap R S)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
  exact (eq_maximalIdeal this).ge

end S_IsLocalRing_map_maximalIdeal_le_jacobson_bot_of_isIntegral
end P2MW
export P2MW.S_IsLocalRing_map_maximalIdeal_le_jacobson_bot_of_isIntegral (solution)
