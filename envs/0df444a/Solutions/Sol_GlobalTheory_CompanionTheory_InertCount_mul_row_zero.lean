-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCount.mul_row_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:26:05.803323+00:00
-- url     : https://prove2.me/submissions/e8effcd3-c005-4f68-abd7-1668b18abf43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CountOfHeisenbergIndex
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCount_col_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCount
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q N : ℕ}
namespace GlobalTheory.CompanionTheory.InertCount
theorem _root_.solution (hH : Heis) (hU : IsUnramInv ϖ σ q) {u w : GU σ (N + 2)} (hu : u ∈ radQ σ N)
    (hw : w ∈ radQ σ N) (h0 : rowOf w = 0) :
    rowOf (u * w) = rowOf u ∧ colOf (u * w) = colOf u ∧ cornerOf (u * w) = cornerOf u + cornerOf w := by
  obtain ⟨hr, hc, hk⟩ := (hH L ϖ σ q N hU).2.1 u hu w hw
  have hcz := col_zero hH hU hw h0
  refine ⟨?_, ?_, ?_⟩
  · rw [hr, h0, add_zero]
  · rw [hc, hcz, add_zero]
  · rw [hk, hcz, dotProduct_zero, add_zero]
end GlobalTheory.CompanionTheory.InertCount
