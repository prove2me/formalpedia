-- Prove2me | solution 1 for GlobalTheory.TwoStepUnipotent.st_half
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:31:41.611047+00:00
-- url     : https://prove2.me/submissions/cd042d5f-c16e-48ce-ba88-f4939ad95c36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_TwoStepUnipotentCompactModSubring
import Theorems.Thm_GlobalTheory_TwoStepUnipotent_st_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory GlobalTheory.TwoStepUnipotent
variable {S : Type} [Ring S] (st : S →+ S) (e₁ e₃ h : S)
variable {st e₁ e₃ h}
namespace GlobalTheory.TwoStepUnipotent
theorem _root_.solution (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (hh : h + h = 1) (hc : ∀ x, h * x = x * h) : st h = h := by
  have h2 : st h + st h = 1 := by rw [← map_add, hh, st_one hm hi]
  have hd : (h - st h) + (h - st h) = 0 := by
    calc (h - st h) + (h - st h) = (h + h) - (st h + st h) := by abel
      _ = 0 := by rw [hh, h2, sub_self]
  have h3 : h - st h = 0 := by
    calc h - st h = (h - st h) * (h + h) := by rw [hh, mul_one]
      _ = ((h - st h) + (h - st h)) * h := by rw [mul_add, add_mul]
      _ = 0 := by rw [hd, zero_mul]
  exact (sub_eq_zero.mp h3).symm
end GlobalTheory.TwoStepUnipotent
