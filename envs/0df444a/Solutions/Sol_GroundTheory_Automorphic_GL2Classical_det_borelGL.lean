-- Prove2me | solution 1 for GroundTheory.Automorphic.GL2Classical.det_borelGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:48:48.256536+00:00
-- url     : https://prove2.me/submissions/a6233911-69a1-4a0b-9446-366da8b7aa33

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
theorem _root_.solution (z : ℍ) : (borelGL z).det.val = z.im := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_borelGL, Matrix.det_fin_two_of]
  ring
end GroundTheory.Automorphic.GL2Classical
