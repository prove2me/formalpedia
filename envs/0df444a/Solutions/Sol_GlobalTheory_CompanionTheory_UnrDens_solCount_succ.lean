-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.solCount_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:53:33.644851+00:00
-- url     : https://prove2.me/submissions/35993e5e-ce82-45a8-b92e-0ff1aecd0bf6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResidueAlgebraUnramified
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFibreGramDifferential
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCard
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHermitianRepsCountSucc
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_card_of_fibres
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_fibre_card
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_card_quot_lev


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc
open GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.HenselStep
namespace GlobalTheory.CompanionTheory.UnrDens
theorem _root_.solution : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ),
    IsUnrQuad R σ ϖ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) R)
    (T : Matrix (Fin n) (Fin n) R), IsUnimod σ S → IsUnimod σ T → ∀ k : ℕ, 1 ≤ k →
    solCount σ ϖ S T (k + 1) = solCount σ ϖ S T k * q ^ (2 * m * n - n ^ 2) := by
  intro R _ σ ϖ q ε h m n hnm S T hS hT k hk
  have hfin : ∀ j, Finite (R ⧸ lev ϖ j) := fun j =>
    Nat.finite_of_card_ne_zero (by
      rw [GlobalTheory.CompanionTheory.UnrDens.card_quot_lev R σ ϖ q ε h j]
      exact pow_ne_zero _ (by have := h.one_lt; omega))
  haveI := hfin k
  haveI := hfin (k + 1)
  haveI : Finite (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) := by unfold Matrix; infer_instance
  haveI : Finite (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ (k + 1))) := by unfold Matrix; infer_instance
  unfold solCount
  refine card_of_fibres (down σ ϖ S T k) _ ?_
  rintro ⟨s, x, hx, rfl⟩
  exact fibre_card h hnm hS hT hk hx _ rfl
end GlobalTheory.CompanionTheory.UnrDens
