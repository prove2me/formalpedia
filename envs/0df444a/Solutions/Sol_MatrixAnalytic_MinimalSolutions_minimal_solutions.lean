-- Prove2me | solution 1 for MatrixAnalytic.MinimalSolutions.minimal_solutions
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:59:29.222154+00:00
-- url     : https://prove2.me/submissions/051e00a1-1b4a-425d-8723-95b348f59556
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Chain
import Definitions.Def_MatrixAnalytic_MinimalSolutions_QBD
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Passage
import Theorems.Thm_MatrixAnalytic_MinimalSolutions_ur_minimal_solutions
import Theorems.Thm_MatrixAnalytic_MinimalSolutions_g_riccati_minimal_solutions

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal

open MatrixAnalytic.MinimalSolutions

theorem solution {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    -- (8.13): `(U, R)` solves the system, with convergent series, and is minimal
    ((∀ i j, seriesInvE (matU (qbdP B A₀ A₁ A₂)) i j ≠ ⊤) ∧
      (∀ i j, matR (qbdP B A₀ A₁ A₂) i j ≠ ⊤) ∧
      matU (qbdP B A₀ A₁ A₂) = ennMat A₁ + matMulE (matR (qbdP B A₀ A₁ A₂)) (ennMat A₂) ∧
      matR (qbdP B A₀ A₁ A₂) = matMulE (ennMat A₀) (seriesInvE (matU (qbdP B A₀ A₁ A₂))) ∧
      ∀ X Z : ι → ι → ℝ, (∀ i j, 0 ≤ X i j) → (∀ i j, 0 ≤ Z i j) →
        (∀ i j, seriesInvE (ennMat X) i j ≠ ⊤) →
        ennMat X = ennMat A₁ + matMulE (ennMat Z) (ennMat A₂) →
        ennMat Z = matMulE (ennMat A₀) (seriesInvE (ennMat X)) →
        ∀ i j, matU (qbdP B A₀ A₁ A₂) i j ≤ ennMat X i j ∧
          matR (qbdP B A₀ A₁ A₂) i j ≤ ennMat Z i j) ∧
    -- (8.14): `U` solves the equation, with convergent series, and is minimal
    (matU (qbdP B A₀ A₁ A₂) = ennMat A₁ +
        matMulE (matMulE (ennMat A₀) (seriesInvE (matU (qbdP B A₀ A₁ A₂)))) (ennMat A₂) ∧
      ∀ X : ι → ι → ℝ, (∀ i j, 0 ≤ X i j) →
        (∀ i j, seriesInvE (ennMat X) i j ≠ ⊤) →
        ennMat X = ennMat A₁ + matMulE (matMulE (ennMat A₀) (seriesInvE (ennMat X))) (ennMat A₂) →
        ∀ i j, matU (qbdP B A₀ A₁ A₂) i j ≤ ennMat X i j) ∧
    -- (8.15): `G` is a nonnegative solution and is minimal
    ((∀ i j, matG (qbdP B A₀ A₁ A₂) i j ≠ ⊤) ∧
      matG (qbdP B A₀ A₁ A₂) = ennMat A₂ + matMulE (ennMat A₁) (matG (qbdP B A₀ A₁ A₂)) +
        matMulE (ennMat A₀) (matMulE (matG (qbdP B A₀ A₁ A₂)) (matG (qbdP B A₀ A₁ A₂))) ∧
      ∀ Y : ι → ι → ℝ, (∀ i j, 0 ≤ Y i j) →
        ennMat Y = ennMat A₂ + matMulE (ennMat A₁) (ennMat Y) +
          matMulE (ennMat A₀) (matMulE (ennMat Y) (ennMat Y)) →
        ∀ i j, matG (qbdP B A₀ A₁ A₂) i j ≤ ennMat Y i j) ∧
    -- (8.16): `R` is a nonnegative solution and is minimal
    ((∀ i j, matR (qbdP B A₀ A₁ A₂) i j ≠ ⊤) ∧
      matR (qbdP B A₀ A₁ A₂) = ennMat A₀ + matMulE (matR (qbdP B A₀ A₁ A₂)) (ennMat A₁) +
        matMulE (matMulE (matR (qbdP B A₀ A₁ A₂)) (matR (qbdP B A₀ A₁ A₂))) (ennMat A₂) ∧
      ∀ Z : ι → ι → ℝ, (∀ i j, 0 ≤ Z i j) →
        ennMat Z = ennMat A₀ + matMulE (ennMat Z) (ennMat A₁) +
          matMulE (matMulE (ennMat Z) (ennMat Z)) (ennMat A₂) →
        ∀ i j, matR (qbdP B A₀ A₁ A₂) i j ≤ ennMat Z i j) := by
  rcases MatrixAnalytic.MinimalSolutions.ur_minimal_solutions
      B A₀ A₁ A₂ hP hirr with ⟨h813, h814, h816⟩
  have h815 := MatrixAnalytic.MinimalSolutions.g_riccati_minimal_solutions
      B A₀ A₁ A₂ hP hirr
  exact ⟨h813, h814, h815, h816⟩
