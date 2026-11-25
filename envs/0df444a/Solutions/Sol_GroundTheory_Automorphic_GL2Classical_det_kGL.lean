-- Prove2me | solution 1 for GroundTheory.Automorphic.GL2Classical.det_kGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:48:48.783677+00:00
-- url     : https://prove2.me/submissions/61cad42e-b165-49f8-a61c-d98b32f65d9a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2Classical_Iwasawa

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
theorem _root_.solution (w : ℂ) (hw : w ≠ 0) : (kGL w hw).det.val = Complex.normSq w := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_kGL, det_fin_two_kmat]
end GroundTheory.Automorphic.GL2Classical
