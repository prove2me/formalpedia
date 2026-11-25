-- Prove2me | solution 1 for GroundTheory.Automorphic.GL2Classical.denom_borelGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:48:46.960941+00:00
-- url     : https://prove2.me/submissions/ccb1e0dc-a23f-4ab2-98de-843cdf719696

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2Classical_Iwasawa
import Theorems.Thm_GroundTheory_Automorphic_GL2Classical_coe_borelGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GL2Classical.coe_borelGL

set_option autoImplicit false
open Matrix UpperHalfPlane
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.GL2Classical
namespace GroundTheory.Automorphic.GL2Classical
theorem _root_.solution (z : ℍ) (w : ℂ) : denom (borelGL z) w = 1 := by
  simp [denom]
end GroundTheory.Automorphic.GL2Classical
