-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Div.semilinear_factors_through_reduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:37:44.697473+00:00
-- url     : https://prove2.me/submissions/0585d522-0b26-4067-9b59-18b29cc0f73b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_SemilinearFactorsThroughReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Div
namespace GlobalTheory.CompanionTheory.Div
theorem _root_.solution :
    ∀ (A O : Type) [CommRing A] [CommRing O] (θ : A →+* O), Function.Surjective θ →
      ∀ (ξ : A), θ ξ = 0 →
      ∀ (M D L : Type) [AddCommGroup M] [Module A M] [AddCommGroup D] [Module O D]
        [AddCommGroup L] [Module O L] (r : M →ₛₗ[θ] D) (q : M →ₛₗ[θ] L),
        Function.Surjective r → (∀ m, r m = 0 ↔ ∃ n, m = ξ • n) →
        ∃ π : D →ₗ[O] L, ∀ m, π (r m) = q m := by
  intro A O _ _ θ hθ ξ hξ M D L _ _ _ _ _ _ r q hr hker
  have hq : ∀ m m', r m = r m' → q m = q m' := by
    intro m m' h
    obtain ⟨n, hn⟩ := (hker (m - m')).1 (by rw [map_sub, h, sub_self])
    have h0 : q (m - m') = 0 := by rw [hn, map_smulₛₗ, hξ, zero_smul]
    rwa [map_sub, sub_eq_zero] at h0
  let s := Function.surjInv hr
  have hs : ∀ d, r (s d) = d := Function.surjInv_eq hr
  refine ⟨{ toFun := fun d => q (s d), map_add' := ?_, map_smul' := ?_ }, fun m => hq _ _ (hs _)⟩
  · intro d d'
    rw [← map_add]
    exact hq _ _ (by rw [map_add, hs, hs, hs])
  · intro o d
    obtain ⟨a, rfl⟩ := hθ o
    simp only [RingHom.id_apply]
    rw [← map_smulₛₗ]
    exact hq _ _ (by rw [map_smulₛₗ, hs, hs])
end GlobalTheory.CompanionTheory.Div
