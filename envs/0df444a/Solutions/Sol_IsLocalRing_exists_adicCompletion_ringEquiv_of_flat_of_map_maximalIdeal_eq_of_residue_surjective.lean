-- Prove2me | solution 1 for IsLocalRing.exists_adicCompletion_ringEquiv_of_flat_of_map_maximalIdeal_eq_of_residue_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/e5e2b438-24e5-566e-bee9-8724a175cfc1

import Mathlib
import Theorems.Thm_IsLocalRing_moduleFinite_quotient_maximalIdeal_pow_of_residueField_map_surjective
import Theorems.Thm_IsLocalRing_quotient_mk_comp_algebraMap_surjective_of_map_maximalIdeal_eq_of_residueField_map_surjective
import Theorems.Thm_IsLocalRing_ker_quotient_mk_comp_algebraMap_eq_maximalIdeal_pow_of_flat_of_map_maximalIdeal_eq
import Theorems.Thm_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_adicCompletion_ringEquiv_of_flat_of_map_maximalIdeal_eq_of_residue_surjective

set_option autoImplicit false

theorem solution
    {R S : Type*} [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    (hmax : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S)
    (hres : Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R S))) :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal S) S,
      ∀ r : R, e (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r) =
        algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (algebraMap R S r) :=
  AdicCompletion.exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow
    (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S) (algebraMap R S)
    (fun k => IsLocalRing.quotient_mk_comp_algebraMap_surjective_of_map_maximalIdeal_eq_of_residueField_map_surjective
      hmax hres k)
    (fun k => IsLocalRing.ker_quotient_mk_comp_algebraMap_eq_maximalIdeal_pow_of_flat_of_map_maximalIdeal_eq hmax k)

end S_IsLocalRing_exists_adicCompletion_ringEquiv_of_flat_of_map_maximalIdeal_eq_of_residue_surjective
end P2MW
export P2MW.S_IsLocalRing_exists_adicCompletion_ringEquiv_of_flat_of_map_maximalIdeal_eq_of_residue_surjective (solution)
