-- Prove2me | solution 1 for GlobalTheory.T.norm_fibre_card_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:47:04.02482+00:00
-- url     : https://prove2.me/submissions/4a2fd28e-a3ce-4b64-b4c1-f1e1c689b7e2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardZeroStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormZero_card_norm_zero


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
theorem _root_.solution : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → (Nat.card {a : E // a * τ a = 0} : ℤ) = q * (1 + ε) - ε := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.NormZero.card_norm_zero | exact GlobalTheory.CompanionTheory.UnrDens.NormZero.card_norm_zero | (intros; apply GlobalTheory.CompanionTheory.UnrDens.NormZero.card_norm_zero <;> assumption)
end _root_.GlobalTheory.T
