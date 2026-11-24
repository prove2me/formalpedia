-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.mul_im_pos_of_sign_mul_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:47:09.115991+00:00
-- url     : https://prove2.me/submissions/99f5a63f-2bb7-4ff7-9702-02e31e14a9a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousIsBigORpowLipschitzProductKernel
import Theorems.Thm_GlobalTheory_LipschitzTR_remb_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LipschitzTR.remb_apply



set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.LipschitzTR
namespace GlobalTheory.LipschitzTR
theorem _root_.solution {w : ℂ} {t : ℝ} (h : 0 < (SignType.sign w.im : ℝ) * t) :
    0 < t * w.im := by
  rcases lt_trichotomy w.im 0 with hw | hw | hw
  · rw [sign_neg hw] at h
    simp at h
    nlinarith
  · rw [hw, sign_zero] at h
    simp at h
  · rw [sign_pos hw] at h
    simp at h
    positivity
end GlobalTheory.LipschitzTR
