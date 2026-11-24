-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ModuleReduction.mem_smul_of_tmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:52:49.143801+00:00
-- url     : https://prove2.me/submissions/5268b2d1-f3e4-4ddf-87f4-a8c55a095f85

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_MemSmulOfTmulEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct ChangeOfRings
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ModuleReduction
namespace GlobalTheory.CompanionTheory.ModuleReduction
theorem _root_.solution {A Q N : Type} [CommRing A] [AddCommGroup Q] [Module A Q]
    [AddCommGroup N] [Module A N] (g : A →ₗ[A] Q) (hg : Function.Surjective g) (ξ : A)
    (hk : ∀ a, g a = 0 ↔ ∃ b, a = ξ * b) (m : N) (h : g 1 ⊗ₜ[A] m = 0) :
    ∃ n : N, m = ξ • n := by
  have hex : Function.Exact (LinearMap.mulLeft A ξ) g := by
    intro a
    rw [hk a]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨b, rfl⟩
  have hex' := rTensor_exact N hex hg
  have h1 : (LinearMap.rTensor N g) ((1 : A) ⊗ₜ[A] m) = 0 := by
    simpa using h
  obtain ⟨t, ht⟩ := (hex' _).1 h1
  have key : ∀ t : A ⊗[A] N, TensorProduct.lid A N (LinearMap.rTensor N (LinearMap.mulLeft A ξ) t)
      = ξ • TensorProduct.lid A N t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a n => simp [mul_smul]
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  refine ⟨TensorProduct.lid A N t, ?_⟩
  rw [← key, ht]
  simp
end GlobalTheory.CompanionTheory.ModuleReduction
