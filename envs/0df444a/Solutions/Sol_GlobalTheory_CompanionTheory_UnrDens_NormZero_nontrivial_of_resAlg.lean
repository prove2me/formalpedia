-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.NormZero.nontrivial_of_resAlg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:52:06.20979+00:00
-- url     : https://prove2.me/submissions/793e6888-972c-49d4-8701-0c528c3548c2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardZero
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormZero_finite_of_resAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.NormZero
variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}
namespace GlobalTheory.CompanionTheory.UnrDens.NormZero
theorem _root_.solution (h : ResAlg E τ q ε) : Nontrivial E := by
  haveI := finite_of_resAlg h
  apply Finite.one_lt_card_iff_nontrivial.1
  rw [h.card]
  have := h.one_lt
  nlinarith
end GlobalTheory.CompanionTheory.UnrDens.NormZero
