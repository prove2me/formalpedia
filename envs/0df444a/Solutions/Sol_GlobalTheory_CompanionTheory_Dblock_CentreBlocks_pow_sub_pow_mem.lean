-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Dblock.CentreBlocks.pow_sub_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:40:51.9733+00:00
-- url     : https://prove2.me/submissions/dfc3a164-41e7-4c5d-942a-28bf2d7793ac

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MonicFactorCoefficientsIntegralStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CapelliPolynomialCoefficientsIdeal
import Theorems.Thm_GlobalTheory_CompanionTheory_Dblock_CentreBlocks_pow_apply_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Dblock GlobalTheory.CompanionTheory.Dblock.CentreBlocks
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.Dblock.CentreBlocks
theorem _root_.solution (β D : Module.End ℂ V) (Wn I : Submodule ℂ V)
    (hβ : ∀ F ∈ I, β F ∈ I) (hD : ∀ F ∈ Wn, D F ∈ Wn) (hDβ : ∀ F ∈ Wn, D F - β F ∈ I) :
    ∀ n : ℕ, ∀ F ∈ Wn, (β ^ n) F - (D ^ n) F ∈ I := by
  intro n
  induction n with
  | zero => intro F _; simp
  | succ n ih =>
    intro F hF
    have h1 := hβ _ (ih F hF)
    have h2 := hDβ _ (pow_apply_mem D Wn hD n F hF)
    have : (β ^ (n + 1)) F - (D ^ (n + 1)) F
        = β ((β ^ n) F - (D ^ n) F) - (D ((D ^ n) F) - β ((D ^ n) F)) := by
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, map_sub]
      abel
    rw [this]
    exact I.sub_mem h1 h2
end GlobalTheory.CompanionTheory.Dblock.CentreBlocks
