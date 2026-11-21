-- Prove2me | solution 1 for MasulloGRH.nuclearFrechet_strongBidual_bounded_repr
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:41:51.322382+00:00
-- url     : https://prove2.me/submissions/b3e8d810-6a5d-4410-af5d-52d32e885bbb

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_bounded_iff_weakly_bounded
import Theorems.Thm_MasulloGRH_nuclearFrechet_strongBidual_eval

set_option autoImplicit false

open MasulloGRH

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) (hN : IsNuclear E)
    (q : Seminorm ℂ (StrongDual ℂ E)) (hq : Continuous q) :
    ∃ D : Set E, Bornology.IsVonNBounded ℂ D ∧
      ∀ F : StrongDual ℂ (StrongDual ℂ E), (∀ f, ‖F f‖ ≤ q f) →
        ∃ y ∈ D, ∀ f : StrongDual ℂ E, F f = f y := by
  refine ⟨{y | ∀ f : StrongDual ℂ E, ‖f y‖ ≤ q f}, ?_, ?_⟩
  · rw [bounded_iff_weakly_bounded E ⟨hE.1, hE.2.1.1⟩]
    intro ℓ
    rw [isBounded_iff_forall_norm_le]
    refine ⟨q ℓ, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hy ℓ
  · intro F hF
    obtain ⟨y, hy⟩ := nuclearFrechet_strongBidual_eval E hE hN F
    refine ⟨y, fun f => ?_, hy⟩
    rw [← hy f]
    exact hF f
