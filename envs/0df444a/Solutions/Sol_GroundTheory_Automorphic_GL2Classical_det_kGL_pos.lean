-- Prove2me | solution 1 for GroundTheory.Automorphic.GL2Classical.det_kGL_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:55:26.125334+00:00
-- url     : https://prove2.me/submissions/94d3a916-adfb-422e-9c92-7368db2b3ca9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2Classical_Iwasawa
import Theorems.Thm_GroundTheory_Automorphic_GL2Classical_det_kGL

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
theorem _root_.solution (w : ℂ) (hw : w ≠ 0) : 0 < (kGL w hw).det.val := by
  rw [det_kGL]
  exact Complex.normSq_pos.2 hw
end GroundTheory.Automorphic.GL2Classical
