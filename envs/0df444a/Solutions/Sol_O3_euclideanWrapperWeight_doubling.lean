-- Prove2me | solution 1 for O3.euclideanWrapperWeight_doubling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:30:26.265149+00:00
-- url     : https://prove2.me/submissions/1018d1d5-09ad-43ab-b236-0c6062bc5545

import Definitions.Def_O3_AboveTwo
import Definitions.Def_O3_Stage11Amortization

set_option autoImplicit true
open O3
namespace O3
theorem _root_.solution :
    DoublingWeight euclideanWrapperWeight (Real.sqrt 2) := by
  have hsqrt : 1 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  refine ⟨hsqrt, ?_, ?_, ?_⟩
  · intro x hx
    exact Real.sqrt_nonneg _
  · intro x hx y hy hxy
    exact Real.sqrt_le_sqrt hxy
  · intro x hx
    unfold euclideanWrapperWeight
    rw [show 2 * x = 2 * x by rfl, Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
end O3
