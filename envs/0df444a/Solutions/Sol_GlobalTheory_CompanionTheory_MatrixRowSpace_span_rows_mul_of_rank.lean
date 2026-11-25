-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MatrixRowSpace.span_rows_mul_of_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:37:15.54188+00:00
-- url     : https://prove2.me/submissions/c127e989-e4e8-43da-a136-168b5e419a9b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RangeVecMulLinearEq
import Theorems.Thm_GlobalTheory_CompanionTheory_MatrixRowSpace_range_vecMulLinear_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_MatrixRowSpace_span_rows_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_MatrixRowSpace_span_rows_eq_top_iff

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
theorem _root_.solution {m n r : ℕ} (x : Matrix (Fin m) (Fin r) K)
    (c : Matrix (Fin r) (Fin n) K) (hx : x.rank = r) :
    Submodule.span K (Set.range (x * c)) = Submodule.span K (Set.range c) := by
  rw [span_rows_mul, (span_rows_eq_top_iff x).mp hx, Submodule.map_top, range_vecMulLinear_eq]
end GlobalTheory.CompanionTheory.MatrixRowSpace
