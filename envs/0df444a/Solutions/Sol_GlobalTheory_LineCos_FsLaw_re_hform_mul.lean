-- Prove2me | solution 1 for GlobalTheory.LineCos.FsLaw.re_hform_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:08:31.788798+00:00
-- url     : https://prove2.me/submissions/08895e25-eb09-4e1b-a7c8-fb599092e9c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StereographicMeasureChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusChangeOfVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CosineSquarePushforwardUniform

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder ENNReal
noncomputable section
open GlobalTheory GlobalTheory.LineCos GlobalTheory.LineCos.FsLaw
open GlobalTheory.LineCos
namespace GlobalTheory.LineCos.FsLaw
theorem _root_.solution {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) (w : Fin 2 → ℂ) :
    (hform G w w).re * (G 0 0).re = ‖w 0 * G 0 0 + w 1 * G 1 0‖ ^ 2 + G.det.re * ‖w 1‖ ^ 2 := by
  have h00 : (G 0 0).im = 0 := Complex.conj_eq_iff_im.1 (hG.isHermitian.apply 0 0)
  have h11 : (G 1 1).im = 0 := Complex.conj_eq_iff_im.1 (hG.isHermitian.apply 1 1)
  have h01 : G 0 1 = starRingEnd ℂ (G 1 0) := (hG.isHermitian.apply 0 1).symm
  simp only [hform, Fin.sum_univ_two, Matrix.det_fin_two, h01, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.conj_re, Complex.conj_im,
    h00, h11]
  ring
end GlobalTheory.LineCos.FsLaw
