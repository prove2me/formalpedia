-- Prove2me | solution 1 for GroundTheory.Automorphic.GL2Classical.re_smul_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:48:51.926413+00:00
-- url     : https://prove2.me/submissions/74a07453-1ad5-4d74-b014-319bca292ac9

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
theorem _root_.solution {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) :
    (h • I).re = ((h : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * h 1 0 + h 0 1 * h 1 1) /
      Complex.normSq (denom h (I : ℂ)) := by
  rw [UpperHalfPlane.re, coe_smul_of_det_pos hpos, Complex.div_re]
  simp only [num, denom, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, coe_I, Complex.I_re, Complex.I_im]
  ring
end GroundTheory.Automorphic.GL2Classical
