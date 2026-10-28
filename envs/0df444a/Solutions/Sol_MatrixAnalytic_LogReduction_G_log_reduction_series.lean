-- Prove2me | solution 1 for MatrixAnalytic.LogReduction.G_log_reduction_series
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T12:52:50.130894+00:00
-- url     : https://prove2.me/submissions/a03183cd-f524-4c7d-9625-1953b5c180e8

import Mathlib
import Definitions.Def_MatrixAnalytic_LogReduction_Chain
import Definitions.Def_MatrixAnalytic_LogReduction_QBD
import Definitions.Def_MatrixAnalytic_LogReduction_Passage
import Theorems.Thm_MatrixAnalytic_LogReduction_G_band_decomposition
import Theorems.Thm_MatrixAnalytic_LogReduction_products_first_passage
import Theorems.Thm_MatrixAnalytic_LogReduction_HL_first_passage

open scoped ENNReal

open MatrixAnalytic.LogReduction in
theorem solution {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    (∀ i j : ι, seriesInvE (ennMat A₁) i j ≠ ⊤) ∧
    (∀ k : ℕ, ∀ i j : ι, seriesInvE (logU A₀ A₁ A₂ k) i j ≠ ⊤) ∧
    ∀ i j : ι, matG (qbdP B A₀ A₁ A₂) i j =
      ∑' k : ℕ, matMulE (prodH A₀ A₁ A₂ k) (logL A₀ A₁ A₂ k) i j := by
  have hHL := MatrixAnalytic.LogReduction.HL_first_passage B A₀ A₁ A₂ hP hirr
  have hPF := MatrixAnalytic.LogReduction.products_first_passage B A₀ A₁ A₂ hP hirr
  have hG := MatrixAnalytic.LogReduction.G_band_decomposition B A₀ A₁ A₂ hP hirr
  refine ⟨hHL.1, fun k => (hHL.2 k).2.2.2, fun i j => ?_⟩
  rw [hG i j]
  congr 1
  funext k
  rw [(hPF k).2]
