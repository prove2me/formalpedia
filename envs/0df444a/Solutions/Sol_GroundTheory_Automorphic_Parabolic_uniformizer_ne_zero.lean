-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.uniformizer_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:14:19.993979+00:00
-- url     : https://prove2.me/submissions/d93e8362-8e4f-4dcf-ab11-63983a185d60

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution : (GLnLocal.uniformizer F : F) ≠ 0 :=
  coe_uniformizerUnit F ▸ (uniformizerUnit F).ne_zero
end GroundTheory.Automorphic.Parabolic
