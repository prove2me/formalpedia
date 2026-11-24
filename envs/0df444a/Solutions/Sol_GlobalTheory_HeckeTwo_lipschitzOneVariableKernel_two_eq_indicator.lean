-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.lipschitzOneVariableKernel_two_eq_indicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:23:11.910891+00:00
-- url     : https://prove2.me/submissions/ddd2b5cf-1b47-4c7d-ba36-e1a969d4e7fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierLipschitzOneVariableKernelEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousIsBigORpowLipschitzProductKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformSigmaZeroEq
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
noncomputable section
open Complex MeasureTheory Set
open scoped FourierTransform
open GlobalTheory GlobalTheory.HeckeTwo
namespace GlobalTheory.HeckeTwo
theorem _root_.solution {y : ℝ} (hy : 0 < y) :
    GlobalTheory.LipschitzTR.phi1 2 ((y : ℂ) * I) =
      (Ioi (0 : ℝ)).indicator (fun t : ℝ => (t : ℂ) ^ 1 * Complex.exp (-(((2 * Real.pi * y : ℝ) : ℂ) * t))) := by
  funext t
  have him : ((y : ℂ) * I).im = y := by simp
  simp only [GlobalTheory.LipschitzTR.phi1, Set.indicator, Set.mem_Ioi, him, sign_pos hy, SignType.coe_one, one_mul]
  by_cases ht : 0 < t
  · rw [if_pos ht, if_pos ht, abs_of_pos ht]
    push_cast
    congr 2
    ring_nf
    rw [I_sq]
    ring
  · rw [if_neg ht, if_neg ht]
end GlobalTheory.HeckeTwo
