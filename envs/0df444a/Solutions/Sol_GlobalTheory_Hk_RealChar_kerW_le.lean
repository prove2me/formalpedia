-- Prove2me | solution 1 for GlobalTheory.Hk.RealChar.kerW_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:58.975299+00:00
-- url     : https://prove2.me/submissions/ea7073d7-3320-4c01-8f67-aafcd2721d8a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormRayClassFamilyFOneGeOfRealCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RealChar
namespace GlobalTheory.Hk.RealChar
theorem _root_.solution {y w : ℝ} (hy : 0 < y) (hw : 0 < w) :
    kerW y w ≤ 6 / y ^ 3 * (Real.exp (-w) * w ^ ((3 : ℝ) - 1)) := by
  have h := Real.pow_div_factorial_le_exp (y / w) (by positivity) 3
  have h3 : w ^ ((3 : ℝ) - 1) = w ^ 2 := by
    rw [show (3 : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h1 : Real.exp (-(y / w)) ≤ 6 * w ^ 3 / y ^ 3 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
    refine le_trans (le_of_eq ?_) h
    simp only [Nat.factorial]
    field_simp
    norm_num
  rw [h3]
  unfold kerW
  calc Real.exp (-(y / w)) * Real.exp (-w) / w ≤ 6 * w ^ 3 / y ^ 3 * Real.exp (-w) / w := by
        gcongr
    _ = _ := by field_simp
end GlobalTheory.Hk.RealChar
