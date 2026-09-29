-- Prove2me | solution 1 for ModularCurve.transcendental_jq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/3941aa83-1eb9-56a4-b9b3-5023ee22452b

import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_aeval_jq_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_transcendental_jq

open ModularCurve IntermediateField

noncomputable section

theorem solution : Transcendental ℚ jq :=
  transcendental_iff.mpr fun _ hp => ModularCurve.aeval_jq_eq_zero hp

end

end S_ModularCurve_transcendental_jq
end P2MW
export P2MW.S_ModularCurve_transcendental_jq (solution)
