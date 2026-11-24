-- Prove2me | solution 1 for GlobalTheory.Hk.RealChar.summable_th
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:37:17.198138+00:00
-- url     : https://prove2.me/submissions/2c388c7d-7096-41e2-b665-803f25912462

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
theorem _root_.solution {a : ℕ → ℝ} {D : ℝ} (ha : ∀ n, |a n| ≤ D * n) {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℕ => ‖a n * Real.exp (-(t * n))‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((Real.summable_pow_mul_exp_neg_nat_mul 1 ht).mul_left D)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le, pow_one, ← mul_assoc, neg_mul]
  gcongr
  exact ha n
end GlobalTheory.Hk.RealChar
