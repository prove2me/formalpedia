-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IntermediateField.norm_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:48:11.699811+00:00
-- url     : https://prove2.me/submissions/4757a07e-2e76-4146-a102-6f715b0fac19

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltMap
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {K C : Type*} [NontriviallyNormedField K] [NormedField C] [NormedAlgebra K C]
namespace GroundTheory.PAdicHodge
namespace IntermediateField
theorem _root_.solution (F : IntermediateField K C) (x : F) : ‖(x : C)‖ = ‖x‖ :=
  rfl
end IntermediateField
end GroundTheory.PAdicHodge
