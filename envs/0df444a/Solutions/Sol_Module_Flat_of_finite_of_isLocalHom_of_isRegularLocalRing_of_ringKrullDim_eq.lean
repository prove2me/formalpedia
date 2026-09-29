-- Prove2me | solution 1 for Module.Flat.of_finite_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/aba74b72-edce-5c69-a54b-10fc1e671e18

import Mathlib
import Definitions.Def_Patching_SystemTypes
import Theorems.Thm_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing
import Theorems.Thm_Module_depth_eq_depth_of_finite_of_isLocalHom
import Theorems.Thm_IsRegularLocalRing_depth_self_eq_ringKrullDim
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Flat_of_finite_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_eq

set_option autoImplicit false

open IsLocalRing RingTheory

theorem solution
    (R S : Type*) [CommRing R] [CommRing S] [IsNoetherianRing R]
    [IsRegularLocalRing R] [IsRegularLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Finite R S]
    (hdim : ringKrullDim S = ringKrullDim R) :
    Module.Flat R S := by
  haveI : IsNoetherianRing S :=
    isNoetherian_of_tower R (isNoetherian_of_isNoetherianRing_of_finite R S)
  have hdepth : Module.depth R S = Module.depth S S :=
    Module.depth_eq_depth_of_finite_of_isLocalHom R S S
  have hCM : (Module.depth S S : WithBot ℕ∞) = ringKrullDim S :=
    IsRegularLocalRing.depth_self_eq_ringKrullDim S
  have hkey : (Module.depth R S : WithBot ℕ∞) = ringKrullDim R := by
    rw [hdepth, hCM, hdim]
  haveI := Module.free_of_depth_eq_ringKrullDim_of_isRegularLocalRing R S hkey
  infer_instance

end S_Module_Flat_of_finite_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_eq
end P2MW
export P2MW.S_Module_Flat_of_finite_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_eq (solution)
