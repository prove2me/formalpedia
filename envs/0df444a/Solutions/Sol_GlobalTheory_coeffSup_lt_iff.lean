-- Prove2me | solution 1 for GlobalTheory.coeffSup_lt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:31:50.234062+00:00
-- url     : https://prove2.me/submissions/b7555c4d-e997-4323-a646-c12dde58cbbd

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
theorem _root_.solution (h0 : N 0 = 0) {c : ι →₀ M} {γ : Γ₀} (hγ : γ ≠ 0) :
    coeffSup N c < γ ↔ ∀ i, N (c i) < γ := by
  have hγ' : (⊥ : Γ₀) < γ := by rw [bot_eq_zero]; exact zero_lt_iff.mpr hγ
  rw [coeffSup, Finset.sup_lt_iff hγ']
  refine ⟨fun h i => ?_, fun h i _ => h i⟩
  by_cases hi : i ∈ c.support
  · exact h i hi
  · rw [Finsupp.notMem_support_iff.mp hi, h0]; exact zero_lt_iff.mpr hγ
end GlobalTheory
