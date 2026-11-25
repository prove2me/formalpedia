-- Prove2me | solution 1 for GroundTheory.Automorphic.GL2Classical.det_borelGL_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:55:24.775496+00:00
-- url     : https://prove2.me/submissions/7a651e75-e1b8-4d6f-a8fc-b2c1c3b624a3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2Classical_Iwasawa
import Theorems.Thm_GroundTheory_Automorphic_GL2Classical_det_borelGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix UpperHalfPlane
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.GL2Classical
namespace GroundTheory.Automorphic.GL2Classical
theorem _root_.solution (z : ℍ) : 0 < (borelGL z).det.val := by
  rw [det_borelGL]
  exact z.im_pos
end GroundTheory.Automorphic.GL2Classical
