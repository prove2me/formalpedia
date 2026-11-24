-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MatrixRowSpace.span_rows_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:10:47.595834+00:00
-- url     : https://prove2.me/submissions/3d449421-00b4-40ac-b2cc-8464c509ee64

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RangeVecMulLinearEq
import Theorems.Thm_GlobalTheory_CompanionTheory_MatrixRowSpace_row_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MatrixRowSpace
variable {K : Type} [Field K]
namespace GlobalTheory.CompanionTheory.MatrixRowSpace
theorem _root_.solution {m n r : ℕ} (x : Matrix (Fin m) (Fin r) K) (c : Matrix (Fin r) (Fin n) K) :
    Submodule.span K (Set.range (x * c)) =
      (Submodule.span K (Set.range x)).map c.vecMulLinear := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [row_mul]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, ← row_mul]
    exact Submodule.subset_span ⟨i, rfl⟩
end GlobalTheory.CompanionTheory.MatrixRowSpace
