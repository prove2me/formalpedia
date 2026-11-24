-- Prove2me | solution 1 for GlobalTheory.Hk.RaySq.r_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:51:56.121955+00:00
-- url     : https://prove2.me/submissions/d766fdc0-1d1c-4b56-aa9f-ad8385cc5af0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ConvRealChar
import Theorems.Thm_GlobalTheory_Hk_RaySq_r_step

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
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RaySq
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Hk.RaySq
theorem _root_.solution (f : Ideal (𝓞 K) → ℝ) (hf : ∀ I J, f (I * J) = f I * f J) {P C : Ideal (𝓞 K)} (hP : Prime P) (hC : C ≠ 0)
    (hPC : ¬ P ∣ C) (k : ℕ) : r f (P ^ k * C) = (∑ i ∈ Finset.range (k + 1), f P ^ i) * r f C := by
  have hg : ∀ m : ℕ, ∑ i ∈ Finset.range (m + 1), f P ^ i = f P * ∑ i ∈ Finset.range m, f P ^ i + 1 := by
    intro m
    rw [Finset.sum_range_succ', Finset.mul_sum]
    simp only [pow_succ', pow_zero]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [r_step f hf hP hC hPC k, ih, hg (k + 1)]
    ring
end GlobalTheory.Hk.RaySq
