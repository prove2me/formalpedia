-- Prove2me | solution 1 for GroundTheory.Automorphic.GL2Classical.borelGL_smul_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:43:16.923611+00:00
-- url     : https://prove2.me/submissions/f06890d5-3b6d-42a0-b25b-3f49fa830a2f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2Classical_Iwasawa
import Theorems.Thm_GroundTheory_Automorphic_GL2Classical_coe_borelGL
import Theorems.Thm_GroundTheory_Automorphic_GL2Classical_det_borelGL_pos
import Theorems.Thm_GroundTheory_Automorphic_GL2Classical_denom_borelGL
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
theorem _root_.solution (z : ℍ) : borelGL z • I = z := by
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (det_borelGL_pos z), denom_borelGL, div_one, num]
  apply Complex.ext <;> simp
end GroundTheory.Automorphic.GL2Classical
