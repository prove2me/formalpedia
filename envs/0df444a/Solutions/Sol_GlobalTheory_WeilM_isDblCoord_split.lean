-- Prove2me | solution 1 for GlobalTheory.WeilM.isDblCoord_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:08.096518+00:00
-- url     : https://prove2.me/submissions/7b650b06-6540-40b9-9e6b-25eb759ba8b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm
import Theorems.Thm_GlobalTheory_WeilM_splitDarboux_e
import Theorems.Thm_GlobalTheory_WeilM_flat_fromCols

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped NNReal Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R]
variable {α β κ : Type}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
namespace GlobalTheory.WeilM
theorem _root_.solution {JA : Matrix α α (R × R)} {JB : Matrix β β (R × R)} (hA : IsHerm (swapA R) JA)
    (hB : IsHerm (swapA R) JB) (σ : κ ≃ α × β) :
    IsDblCoord (swapA R) (1, -1) JA JB (splitDarboux hA hB σ) (splitDarboux hA hB.dbl (dblNum σ)) := by
  intro w₁ w₂
  have hd : (cmp₁ (dbl JB))ᵀ = fromBlocks (cmp₁ JB)ᵀ 0 0 (-(cmp₁ JB)ᵀ) := by
    ext (i | i) (j | j) <;> simp [dbl]
  simp only [splitDarboux_e]
  rw [hd]
  simp only [Matrix.fromCols_map, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks, flat_fromCols,
    Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg, map_neg]
  try rfl
end GlobalTheory.WeilM
