-- Prove2me | solution 1 for GlobalTheory.exists_coeffSup_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:01.96946+00:00
-- url     : https://prove2.me/submissions/44eb90b6-d1cc-4e32-95f1-86b154440030

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
variable {ι M Γ₀ : Type*} [Zero M] [LinearOrderedCommMonoidWithZero Γ₀]
variable {N : M → Γ₀}
namespace GlobalTheory
theorem _root_.solution [Nonempty ι] (h0 : N 0 = 0) (c : ι →₀ M) :
    ∃ i, coeffSup N c = N (c i) := by
  by_cases hc : c = 0
  · exact ⟨Classical.arbitrary ι, by simp [hc, h0]⟩
  · obtain ⟨i, -, hi⟩ := exists_mem_support_coeffSup_eq (N := N) hc
    exact ⟨i, hi⟩
end GlobalTheory
