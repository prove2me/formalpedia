-- Prove2me | solution 1 for GlobalTheory.T.exists_skewHermitian_add_blockTriangular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:08:10.166866+00:00
-- url     : https://prove2.me/submissions/d8dc208f-f464-4a92-9aaf-1ae5ed7d57f1

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CartanDecompositionLieAlgebra
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CartanDecompositionLieAlgebraStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_IwasawaGen_skew_add_upper


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Filter
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ), Antitone h → (∀ (f : ℝ → ℝ), ∀ X ∈ 𝔤, (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) ∈ 𝔤) → (∀ X ∈ 𝔤, Xᴴ ∈ 𝔤) → (∀ Y ∈ 𝔤, Yᴴ = Y → Matrix.diagonal (fun i => (h i : ℂ)) * Y = Y * Matrix.diagonal (fun i => (h i : ℂ)) → Y.IsDiag) → ∀ X ∈ 𝔤, ∃ A ∈ 𝔤, ∃ B ∈ 𝔤, X = A + B ∧ Aᴴ = -A ∧ B.BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.IwasawaGen.skew_add_upper | exact GlobalTheory.CompanionTheory.IwasawaGen.skew_add_upper | (intros; apply GlobalTheory.CompanionTheory.IwasawaGen.skew_add_upper <;> assumption)
end _root_.GlobalTheory.T
