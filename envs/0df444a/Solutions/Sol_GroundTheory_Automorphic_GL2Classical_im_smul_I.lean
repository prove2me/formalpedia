-- Prove2me | solution 1 for GroundTheory.Automorphic.GL2Classical.im_smul_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:48:49.388095+00:00
-- url     : https://prove2.me/submissions/f867afc1-2d10-44fb-b138-091a3c8184a2

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
theorem _root_.solution {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) :
    (h • I).im = h.det.val / Complex.normSq (denom h (I : ℂ)) := by
  rw [im_smul_eq_div_normSq, abs_of_pos hpos, I_im, mul_one]
end GroundTheory.Automorphic.GL2Classical
