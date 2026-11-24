-- Prove2me | solution 1 for GlobalTheory.T.norm_fibre_card_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:28:30.239856+00:00
-- url     : https://prove2.me/submissions/70ff6c9b-b9b7-472d-8263-43c8d29540a4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzeroStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_card_fibre


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
theorem _root_.solution : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ t : E, τ t = t → t ≠ 0 → (Nat.card {a : E // a * τ a = t} : ℤ) = q - ε := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.NormUnit.card_fibre | exact GlobalTheory.CompanionTheory.UnrDens.NormUnit.card_fibre | (intros; apply GlobalTheory.CompanionTheory.UnrDens.NormUnit.card_fibre <;> assumption)
end _root_.GlobalTheory.T
