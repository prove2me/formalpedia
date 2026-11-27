-- Prove2me | solution 1 for GroundTheory.Automorphic.GL2Classical.kGL_smul_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:44:21.603946+00:00
-- url     : https://prove2.me/submissions/e13141a4-9b22-4eb4-a338-c1f306335020

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2Classical_Iwasawa
import Theorems.Thm_GroundTheory_Automorphic_GL2Classical_det_kGL_pos
import Theorems.Thm_GroundTheory_Automorphic_GL2Classical_denom_kGL

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
theorem _root_.solution (w : ℂ) (hw : w ≠ 0) : kGL w hw • I = I := by
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (det_kGL_pos w hw), denom_kGL, div_eq_iff hw]
  rw [num]
  apply Complex.ext <;> simp
end GroundTheory.Automorphic.GL2Classical
