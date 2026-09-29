-- Prove2me | solution 1 for ModularCurve.jGeomGen_eq_mk_jqModC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/ab459ede-a680-5516-baa3-997dc977ce73

import Mathlib
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_jGeomGen_eq_mk_jqModC
set_option autoImplicit false

open ModularCurve

theorem solution (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    jGeomGen K N = ⟨jqModC K, jqModC_mem K N⟩ := rfl

end S_ModularCurve_jGeomGen_eq_mk_jqModC
end P2MW
export P2MW.S_ModularCurve_jGeomGen_eq_mk_jqModC (solution)
