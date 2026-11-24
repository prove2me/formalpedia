-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.abs_pow_mul_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:45:11.622894+00:00
-- url     : https://prove2.me/submissions/d281a278-0ba2-4df0-82f4-3b0c6f721a5f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousIsBigORpowLipschitzProductKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.LipschitzTR
namespace GlobalTheory.LipschitzTR
theorem _root_.solution (n : ℕ) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    |t| ^ n * Real.exp (-a * |t|) ≤ (n.factorial * (2 / a) ^ n) * Real.exp (-(a / 2) * |t|) := by
  have h := Real.pow_div_factorial_le_exp (a / 2 * |t|) (by positivity) n
  rw [div_le_iff₀ (by positivity)] at h
  have h1 : |t| ^ n ≤ n.factorial * (2 / a) ^ n * Real.exp (a / 2 * |t|) := by
    calc |t| ^ n = (2 / a) ^ n * (a / 2 * |t|) ^ n := by
          rw [← mul_pow]; congr 1; field_simp
      _ ≤ (2 / a) ^ n * (Real.exp (a / 2 * |t|) * n.factorial) := by gcongr
      _ = _ := by ring
  calc |t| ^ n * Real.exp (-a * |t|)
      ≤ (n.factorial * (2 / a) ^ n * Real.exp (a / 2 * |t|)) * Real.exp (-a * |t|) := by gcongr
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
end GlobalTheory.LipschitzTR
