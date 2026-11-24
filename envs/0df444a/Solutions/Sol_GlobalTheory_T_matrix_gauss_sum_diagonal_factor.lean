-- Prove2me | solution 1 for GlobalTheory.T.matrix_gauss_sum_diagonal_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:18:22.238704+00:00
-- url     : https://prove2.me/submissions/6a043fa3-dbe9-4c18-a44f-b1ec3a170787

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MatrixGaussSumDiagonalFactor
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MatrixGaussSumDiagonalFactorStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_GaussProd_gauss_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ) (k : ℕ) [Fintype (R ⧸ lev ϖ k)] (χ : AddChar (R ⧸ lev ϖ k) ℂ) (m n : ℕ) (D : Fin n → R) (E : Fin m → R), (∑ y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), χ (Matrix.trace (red ϖ k (Matrix.diagonal D) * (cT (barσ σ ϖ hf k) y * red ϖ k (Matrix.diagonal E) * y)))) = ∏ i : Fin n, ∏ l : Fin m, ∑ w : R ⧸ lev ϖ k, χ (Ideal.Quotient.mk (lev ϖ k) (E l * D i) * (barσ σ ϖ hf k w * w)) := by
  first | exact @GlobalTheory.CompanionTheory.GaussProd.gauss_prod | exact GlobalTheory.CompanionTheory.GaussProd.gauss_prod | (intros; apply GlobalTheory.CompanionTheory.GaussProd.gauss_prod <;> assumption)
end _root_.GlobalTheory.T
