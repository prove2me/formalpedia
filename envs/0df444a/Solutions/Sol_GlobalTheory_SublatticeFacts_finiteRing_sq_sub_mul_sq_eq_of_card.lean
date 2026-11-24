-- Prove2me | solution 1 for GlobalTheory.SublatticeFacts.finiteRing_sq_sub_mul_sq_eq_of_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:58:43.659375+00:00
-- url     : https://prove2.me/submissions/c8c69a5a-5503-42a2-888e-d92701ecc921

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBisExtra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SublatticeFacts
open Matrix
namespace GlobalTheory.SublatticeFacts
theorem _root_.solution {A : Type} [CommRing A] {S : Subring A} {n : Type} [Fintype n] [DecidableEq n]
    (Λ : Submodule (↥S) (n → A)) (hfg : Submodule.FG Λ)
    (hden : ∀ (v : n → A), ∃ (N : ℕ), (1 : ℕ) ≤ N ∧ (↑N : A) • v ∈ Λ) (X : Matrix n n A) :
    ∃ (N : ℕ), (1 : ℕ) ≤ N ∧ ∀ y ∈ Λ, (↑N : A) • Matrix.mulVec X y ∈ Λ := by
  classical
  obtain ⟨t, rfl⟩ := hfg
  choose f hf1 hf using fun v : n → A => hden (X *ᵥ v)
  refine ⟨∏ v ∈ t, f v, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun v _ => by have := hf1 v; omega)
  · intro y hy
    rw [Nat.cast_smul_eq_nsmul A]
    induction hy using Submodule.span_induction with
    | mem x hx =>
      rw [← Finset.mul_prod_erase t f hx, mul_nsmul, ← Nat.cast_smul_eq_nsmul A (f x)]
      exact Submodule.smul_of_tower_mem _ (∏ v ∈ t.erase x, f v) (hf x)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [Matrix.mulVec_add, smul_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have : X *ᵥ (a • x) = a • (X *ᵥ x) := by
        ext i
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum, Subring.smul_def, mul_left_comm]
      rw [this, smul_comm]
      exact Submodule.smul_mem _ a hx
end GlobalTheory.SublatticeFacts
