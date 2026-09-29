-- Prove2me | solution 1 for IsLocalRing.principalUnits_one_eq_ker_map_residue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/6b57b5cc-d9ea-5a35-9313-2423b15b9913

import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_principalUnits_one_eq_ker_map_residue

set_option autoImplicit false
open IsLocalRing

open IsLocalRing in
theorem solution {R : Type*} [CommRing R] [IsLocalRing R] :
    principalUnits R 1 = (Units.map (residue R : R →* ResidueField R)).ker := by
  ext u
  rw [mem_principalUnits_iff, pow_one, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one,
    MonoidHom.coe_coe, ← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]

end S_IsLocalRing_principalUnits_one_eq_ker_map_residue
end P2MW
export P2MW.S_IsLocalRing_principalUnits_one_eq_ker_map_residue (solution)
