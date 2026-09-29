-- Prove2me | solution 1 for ModPForms.modPCusp_le_modPMod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/e71c54fa-b8fe-5a9b-b95d-f8f08238da9c

import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_modPCusp_le_modPMod
set_option autoImplicit false

open ModPForms

theorem solution (N' : ℕ) [NeZero N'] (k : ℤ) (F : Type) [Field F] :
    modPCusp N' k F ≤ modPMod N' k F := by
  refine Submodule.span_mono ?_
  rintro φ ⟨f, a, ha, hφ⟩
  exact ⟨(f : ModularForm (CongruenceSubgroup.Gamma0 N') k), a, ha, hφ⟩

end S_ModPForms_modPCusp_le_modPMod
end P2MW
export P2MW.S_ModPForms_modPCusp_le_modPMod (solution)
