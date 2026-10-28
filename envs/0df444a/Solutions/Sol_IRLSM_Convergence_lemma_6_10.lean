-- Prove2me | solution 1 for IRLSM.Convergence.lemma_6_10
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:58:04.717574+00:00
-- url     : https://prove2.me/submissions/c56550a7-3e1c-413a-bdc3-c482cbf94362

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic
import Theorems.Thm_MinRankRecovery_Recovery_lemma_2_3

open HighDimStat.MatrixRank Matrix
open IRLSM.Convergence

/-- **Lemma 6.10** (Lemma 2.3 of Recht–Fazel–Parrilo). Let `X` and `Z` be matrices of the same
dimensions. If `X Zᵀ = 0` and `Xᵀ Z = 0`, then `‖X + Z‖_* = ‖X‖_* + ‖Z‖_*`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, Lemma 6.10, p. 19.

Formalization Note: real matrices, so `X Z*` is `X * Zᵀ` and `X* Z` is `Xᵀ * Z`. -/
theorem solution {n p : ℕ} (X Z : Matrix (Fin n) (Fin p) ℝ) (h1 : X * Zᵀ = 0)
    (h2 : Xᵀ * Z = 0) : nuclearNorm (X + Z) = nuclearNorm X + nuclearNorm Z := by
  apply MinRankRecovery.Recovery.lemma_2_3 <;> assumption


