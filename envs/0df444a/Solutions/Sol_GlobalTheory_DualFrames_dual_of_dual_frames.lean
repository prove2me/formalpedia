-- Prove2me | solution 1 for GlobalTheory.DualFrames.dual_of_dual_frames
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:32:53.927687+00:00
-- url     : https://prove2.me/submissions/351462bc-a923-4194-aefe-c08571e1c3c3

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DualOfDualFrames
import Theorems.Thm_GlobalTheory_DualFrames_hform_frames
import Theorems.Thm_GlobalTheory_DualFrames_hform_swap
import Theorems.Thm_GlobalTheory_DualFrames_exists_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.UG
open GlobalTheory GlobalTheory.DualFrames
variable {A : Type} [CommRing A] {k : ℕ}
namespace GlobalTheory.DualFrames
theorem _root_.solution :
    ∀ (A : Type) [CommRing A] (S : Subring A) (τ : A →+* A), (∀ a, τ (τ a) = a) →
      (∀ a ∈ S, τ a ∈ S) → ∀ (k : ℕ) (J : Matrix (Fin k) (Fin k) A), IsHerm τ J →
      ∀ (B C : GL (Fin k) A) (L₁ L₂ : Submodule S (Fin k → A)),
      cT τ (B : Matrix (Fin k) (Fin k) A) * J * (C : Matrix (Fin k) (Fin k) A) = 1 →
      (∀ y : Fin k → A, (B : Matrix (Fin k) (Fin k) A) *ᵥ y ∈ L₁ ↔ ∀ i, y i ∈ S) →
      (∀ y : Fin k → A, (C : Matrix (Fin k) (Fin k) A) *ᵥ y ∈ L₂ ↔ ∀ i, y i ∈ S) →
      (∀ y, y ∈ L₂ ↔ ∀ x ∈ L₁, hform τ J x y ∈ S) ∧
      (∀ y, y ∈ L₁ ↔ ∀ x ∈ L₂, hform τ J x y ∈ S) ∧
      (∀ x, x ∈ L₁ ↔ ∀ y ∈ L₂, hform τ J x y ∈ S) := by
  intro A _ S τ hτ hS k J hJ B C L₁ L₂ h hL₁ hL₂

  have pair : ∀ u v : Fin k → A,
      hform τ J ((B : Matrix (Fin k) (Fin k) A) *ᵥ u) ((C : Matrix (Fin k) (Fin k) A) *ᵥ v) =
        ∑ i, τ (u i) * v i :=
    fun u v => hform_frames τ J B C h u v
  have flip : ∀ x y, hform τ J x y = τ (hform τ J y x) :=
    fun x y => (hform_swap τ hτ J hJ y x).symm
  have memS_iff : ∀ a, τ a ∈ S ↔ a ∈ S := fun a =>
    ⟨fun ha => hτ a ▸ hS _ ha, hS a⟩
  have single_mem : ∀ i j, (Pi.single i (1 : A) : Fin k → A) j ∈ S := by
    intro i j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj, S.zero_mem]
  have coord : ∀ u v : Fin k → A, (∀ i, u i ∈ S) → (∀ i, v i ∈ S) → ∑ i, τ (u i) * v i ∈ S :=
    fun u v hu hv => sum_mem fun i _ => mul_mem (hS _ (hu i)) (hv i)
  have part1 : ∀ y, y ∈ L₂ ↔ ∀ x ∈ L₁, hform τ J x y ∈ S := by
    intro y
    obtain ⟨v, rfl⟩ := exists_mulVec C y
    rw [hL₂]
    constructor
    · intro hv x hx
      obtain ⟨u, rfl⟩ := exists_mulVec B x
      rw [pair]
      exact coord u v ((hL₁ u).1 hx) hv
    · intro hall i
      have key := hall ((B : Matrix (Fin k) (Fin k) A) *ᵥ Pi.single i 1) ((hL₁ _).2 (single_mem i))
      have e : ∑ j, τ ((Pi.single i (1 : A) : Fin k → A) j) * v j = v i := by
        simp [Pi.single_apply]
      rwa [pair, e] at key
  have part2 : ∀ y, y ∈ L₁ ↔ ∀ x ∈ L₂, hform τ J x y ∈ S := by
    intro y
    obtain ⟨v, rfl⟩ := exists_mulVec B y
    rw [hL₁]
    constructor
    · intro hv x hx
      obtain ⟨u, rfl⟩ := exists_mulVec C x
      rw [flip, pair, memS_iff]
      exact coord v u hv ((hL₂ u).1 hx)
    · intro hall i
      have key := hall ((C : Matrix (Fin k) (Fin k) A) *ᵥ Pi.single i 1) ((hL₂ _).2 (single_mem i))
      have e : ∑ j, τ (v j) * (Pi.single i (1 : A) : Fin k → A) j = τ (v i) := by
        simp [Pi.single_apply]
      rwa [flip, pair, memS_iff, e, memS_iff] at key
  have part3 : ∀ x, x ∈ L₁ ↔ ∀ y ∈ L₂, hform τ J x y ∈ S := by
    intro x
    rw [part2]
    refine forall₂_congr fun y _ => ?_
    rw [flip x y, memS_iff]
  exact ⟨part1, part2, part3⟩
end GlobalTheory.DualFrames
