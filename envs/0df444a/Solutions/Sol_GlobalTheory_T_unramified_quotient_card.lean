-- Prove2me | solution 1 for GlobalTheory.T.unramified_quotient_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:26:25.481795+00:00
-- url     : https://prove2.me/submissions/e8278ec2-7ac5-4534-a50a-92af401c05fa

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCard
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_card_quot_lev


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ k : ℕ, Nat.card (R ⧸ lev ϖ k) = q ^ (2 * k) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.card_quot_lev | exact GlobalTheory.CompanionTheory.UnrDens.card_quot_lev | (intros; apply GlobalTheory.CompanionTheory.UnrDens.card_quot_lev <;> assumption)
end _root_.GlobalTheory.T
