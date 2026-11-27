-- Prove2me | solution 1 for GroundTheory.Automorphic.GL2Classical.eq_borelGL_mul_kGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:43:18.450205+00:00
-- url     : https://prove2.me/submissions/c433c2fe-d6c9-4f6d-8d3a-ffbdb8899de4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2Classical_Iwasawa
import Theorems.Thm_GroundTheory_Automorphic_GL2Classical_coe_borelGL
import Theorems.Thm_GroundTheory_Automorphic_GL2Classical_re_smul_I
import Theorems.Thm_GroundTheory_Automorphic_GL2Classical_im_smul_I
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
    h = borelGL (h • I) * kGL (denom h (I : ℂ)) (denom_ne_zero h I) := by
  have hN : Complex.normSq (denom h (I : ℂ)) ≠ 0 :=
    (Complex.normSq_pos.2 (denom_ne_zero h I)).ne'
  have hN' : Complex.normSq (denom h (I : ℂ)) = (h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 + h 1 1 ^ 2 := by
    simp [denom, Complex.normSq_apply]
    ring
  have hdet : h.det.val = (h : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * h 1 1 - h 0 1 * h 1 0 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have hre := re_smul_I hpos
  have him := im_smul_I hpos
  rw [hN'] at hre him
  have hD : (h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 + h 1 1 ^ 2 ≠ 0 := hN' ▸ hN
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, coe_borelGL, coe_kGL]
  have hdr : (denom h (I : ℂ)).re = (h : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by simp [denom]
  have hdi : (denom h (I : ℂ)).im = (h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := by simp [denom]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.zero_eta, Fin.mk_one, hdr, hdi, hre, him, hdet] <;>
    field_simp <;> ring
end GroundTheory.Automorphic.GL2Classical
