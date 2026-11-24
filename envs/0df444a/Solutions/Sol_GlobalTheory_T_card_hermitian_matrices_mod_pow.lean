-- Prove2me | solution 1 for GlobalTheory.T.card_hermitian_matrices_mod_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:04:13.620954+00:00
-- url     : https://prove2.me/submissions/9cfd2389-5b38-4b57-9587-129b244f49b6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardHermitianMatricesModPow
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardHermitianMatricesModPowStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_card_hermMod


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ n k : ℕ, Nat.card (hermMod σ ϖ n k) = q ^ (k * n ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.card_hermMod | exact GlobalTheory.CompanionTheory.UnrDens.card_hermMod | (intros; apply GlobalTheory.CompanionTheory.UnrDens.card_hermMod <;> assumption)
end _root_.GlobalTheory.T
