-- Prove2me | solution 1 for GroundTheory.ProfCoh.Supernatural.ofNat_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:09:56.189673+00:00
-- url     : https://prove2.me/submissions/0e204f1b-46d3-4f3c-99f5-832a08c67b40

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_exp_ofNat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.Supernatural.exp_ofNat

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open GroundTheory.ProfCoh.Supernatural
namespace GroundTheory.ProfCoh.Supernatural
theorem _root_.solution : ofNat 1 = 1 := by ext p; simp
end GroundTheory.ProfCoh.Supernatural
