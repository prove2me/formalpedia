-- Prove2me | solution 1 for GlobalTheory.T.hermitian_matrices_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:12:27.362142+00:00
-- url     : https://prove2.me/submissions/77006941-e3e7-4678-b07e-202cfcba1b1e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianMatricesCard
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianMatricesCardStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_card_hermitian_resAlg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ n : ℕ, Nat.card {H : Matrix (Fin n) (Fin n) E // cT τ H = H} = q ^ (n ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.card_hermitian_resAlg | exact GlobalTheory.CompanionTheory.UnrDens.card_hermitian_resAlg | (intros; apply GlobalTheory.CompanionTheory.UnrDens.card_hermitian_resAlg <;> assumption)
end _root_.GlobalTheory.T
