-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MatrixRowSpace.span_rows_eq_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:52:45.000107+00:00
-- url     : https://prove2.me/submissions/f26513b5-35a7-4eaa-aadf-21b104938158

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RangeVecMulLinearEq

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
theorem _root_.solution {m r : ℕ} (x : Matrix (Fin m) (Fin r) K) :
    x.rank = r ↔ Submodule.span K (Set.range x) = ⊤ := by
  rw [Matrix.rank_eq_finrank_span_row]
  constructor
  · intro h
    exact Submodule.eq_top_of_finrank_eq (h.trans (by simp))
  · intro h
    have h' : Submodule.span K (Set.range x.row) = ⊤ := h
    rw [h', finrank_top]
    simp
end GlobalTheory.CompanionTheory.MatrixRowSpace
