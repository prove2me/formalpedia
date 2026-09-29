-- Prove2me | solution 1 for IsLocalRing.ker_quotient_mk_comp_algebraMap_eq_maximalIdeal_pow_of_flat_of_map_maximalIdeal_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d16f3a76-2e15-567a-8790-66f96e2821a7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_ker_quotient_mk_comp_algebraMap_eq_maximalIdeal_pow_of_flat_of_map_maximalIdeal_eq

set_option autoImplicit false

theorem solution
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    (hmax : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S) (k : ℕ) :
    RingHom.ker ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal S ^ k)).comp (algebraMap R S)) =
      IsLocalRing.maximalIdeal R ^ k := by
  haveI : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [← RingHom.comap_ker, Ideal.mk_ker, ← hmax, ← Ideal.map_pow]
  exact Ideal.comap_map_eq_self_of_faithfullyFlat _

end S_IsLocalRing_ker_quotient_mk_comp_algebraMap_eq_maximalIdeal_pow_of_flat_of_map_maximalIdeal_eq
end P2MW
export P2MW.S_IsLocalRing_ker_quotient_mk_comp_algebraMap_eq_maximalIdeal_pow_of_flat_of_map_maximalIdeal_eq (solution)
