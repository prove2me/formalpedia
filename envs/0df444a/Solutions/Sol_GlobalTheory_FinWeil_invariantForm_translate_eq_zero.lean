-- Prove2me | solution 1 for GlobalTheory.FinWeil.invariantForm_translate_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:07:52.45092+00:00
-- url     : https://prove2.me/submissions/3c9c0d37-e912-46cf-964b-43a1ef5562e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvariantFormNormalizedHeisenbergIntertwinerEq
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_comm
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_swap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}
namespace GlobalTheory.FinWeil
theorem _root_.solution (h : IsHeis σ w γ W) {P Q : X →ₗ[R] X} (hPP : ∀ x, P (P x) = P x)
    (hadj : ∀ x y, γ (P x) y = γ x (Q y)) {C : Submodule R X} (hC : SelfDual γ C) (hQC : ∀ a ∈ C, Q a ∈ C)
    (ℓ : M →ₗ[ℂ] ℂ) (hl : ∀ u m, ℓ (W (Q u) m) = ℓ m) {e : M} (he : Fixes W C e) {z : X} (hz : P z ∉ C) :
    ℓ (W (P z) e) = 0 := by
  have hex : ¬ ∀ a ∈ C, γ (P z) a = 1 := fun H => hz ((hC (P z)).2 H)
  push Not at hex
  obtain ⟨a, ha, hne⟩ := hex
  have hQa : W (Q a) e = e := he _ (hQC a ha)
  have hg : γ (P z) (Q a) = γ (P z) a := by rw [← hadj, hPP]
  have hc : W (Q a) (W (P z) e) = γ (Q a) (P z) • W (P z) e := by rw [h.comm, hQa]
  have key := hl a (W (P z) e)
  rw [hc, map_smul, smul_eq_mul] at key
  have hs : γ (Q a) (P z) ≠ 1 := by
    rw [h.swap, hg]
    intro h1
    exact hne (inv_eq_one.1 h1)
  by_contra h0
  exact hs (mul_right_cancel₀ h0 (key.trans (one_mul _).symm))
end GlobalTheory.FinWeil
