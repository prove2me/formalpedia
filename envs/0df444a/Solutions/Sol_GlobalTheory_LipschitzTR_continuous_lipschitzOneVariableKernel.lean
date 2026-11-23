-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.continuous_lipschitzOneVariableKernel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:13:27.004374+00:00
-- url     : https://prove2.me/submissions/a8501c87-74ce-4dc3-aac6-821ce7296b1e

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
theorem _root_.solution {k : ℕ} (hk : 2 ≤ k) {w : ℂ} (hw : w.im ≠ 0) : Continuous (phi1 k w) := by
  have hg : Continuous fun t : ℝ =>
      ((|t| ^ (k - 1) : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * t * w) := by fun_prop
  show Continuous fun t => if 0 < (SignType.sign w.im : ℝ) * t then
    ((|t| ^ (k - 1) : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * t * w) else 0
  refine continuous_if (fun a ha => ?_) hg.continuousOn continuous_const.continuousOn
  have h0 := frontier_lt_subset_eq (continuous_const (y := (0 : ℝ)))
    (continuous_const.mul continuous_id (f := fun _ : ℝ => (SignType.sign w.im : ℝ))) ha
  simp only [Set.mem_setOf_eq, id] at h0
  have ha0 : a = 0 := by
    rcases mul_eq_zero.1 h0.symm with h | h
    · exfalso
      rcases lt_trichotomy w.im 0 with h' | h' | h'
      · rw [sign_neg h'] at h; norm_num at h
      · exact hw h'
      · rw [sign_pos h'] at h; norm_num at h
    · exact h
  subst ha0
  have : k - 1 ≠ 0 := by omega
  simp [this]
end GlobalTheory.LipschitzTR
