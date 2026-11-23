-- Prove2me | solution 1 for GlobalTheory.Hk.LFam.res_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:43.997502+00:00
-- url     : https://prove2.me/submissions/868d9f78-ec18-4fc0-b2f1-8c639eca8abf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBounds

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
open GlobalTheory GlobalTheory.Hk
namespace GlobalTheory.Hk
namespace LFam
theorem _root_.solution (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) : 𝓕.res χ = ∑ g, χ g * (𝓕.κ : ℂ) := by
  rw [← Finset.sum_mul, AddChar.sum_eq_ite]
  unfold LFam.res
  by_cases h : χ = 1
  · rw [if_pos h, if_pos (show χ = 0 from h)]; push_cast; ring
  · rw [if_neg h, if_neg (show ¬ χ = 0 from h)]; simp
end LFam
end GlobalTheory.Hk
