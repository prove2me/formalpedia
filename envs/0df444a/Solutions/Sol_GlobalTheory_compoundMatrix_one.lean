-- Prove2me | solution 1 for GlobalTheory.compoundMatrix_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:57:48.309673+00:00
-- url     : https://prove2.me/submissions/a4d04a62-9c05-4659-ac6a-39580958af2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_range_subsetEnum
import Theorems.Thm_GlobalTheory_subsetEnum_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Kronecker Topology
open GlobalTheory
variable {l n o : Type*} [LinearOrder l] [LinearOrder n] [LinearOrder o]
namespace GlobalTheory
theorem _root_.solution (k : ℕ) : compoundMatrix k (1 : Matrix n n ℂ) = 1 := by
  ext I J
  rcases eq_or_ne I J with rfl | h
  · rw [one_apply_eq, compoundMatrix, of_apply, submatrix_one _ (subsetEnum_injective I), det_one]
  · rw [one_apply_ne h, compoundMatrix, of_apply]
    obtain ⟨x, hxI, hxJ⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne I J).mp h
    have h1 : x ∈ range (subsetEnum I) := by rw [range_subsetEnum]; exact hxI
    have h2 : x ∉ range (subsetEnum J) := by rw [range_subsetEnum]; exact hxJ
    obtain ⟨i, rfl⟩ := h1
    exact det_eq_zero_of_row_eq_zero i fun j => one_apply_ne fun e => h2 ⟨j, e.symm⟩
end GlobalTheory
