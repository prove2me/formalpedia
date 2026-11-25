-- Prove2me | solution 1 for GroundTheory.PAdicHodge.pow_prime_pow_fix_and_move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:32:33.735896+00:00
-- url     : https://prove2.me/submissions/43fae752-7257-4ea6-a6ae-220d5174ec3d

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_apply_ne_of_isPrimitiveRoot
import Theorems.Thm_GroundTheory_PAdicHodge_pow_prime_fix_cycl_succ
import Theorems.Thm_GroundTheory_PAdicHodge_pow_prime_apply_ne
import Theorems.Thm_GroundTheory_PAdicHodge_exists_isPrimitiveRoot
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hγn : ∀ x ∈ cycl p n, γ x = x) {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ (n + 1)))
    (hγζ : γ ζ ≠ ζ) (j : ℕ) :
    (∀ x ∈ cycl p (n + j), (γ ^ (p ^ j)) x = x) ∧
      ∀ η : PadicAlgCl p, IsPrimitiveRoot η (p ^ (n + j + 1)) → (γ ^ (p ^ j)) η ≠ η := by
  induction j with
  | zero =>
    simp only [pow_zero, pow_one, add_zero]
    exact ⟨hγn, fun η hη => apply_ne_of_isPrimitiveRoot γ hγn hζ hγζ hη⟩
  | succ j ih =>
    obtain ⟨hfix, hmove⟩ := ih
    have hpj : γ ^ (p ^ (j + 1)) = (γ ^ (p ^ j)) ^ p := by rw [pow_succ, pow_mul]
    obtain ⟨η, hη⟩ := exists_isPrimitiveRoot (p := p) (n + j + 1)
    refine ⟨?_, fun η' hη' => ?_⟩
    · rw [hpj, ← add_assoc]
      exact pow_prime_fix_cycl_succ (by omega) _ hfix
    · rw [hpj]
      rw [← add_assoc] at hη'
      exact pow_prime_apply_ne (by omega) _ hfix hη (hmove η hη) hη'
end GroundTheory.PAdicHodge
