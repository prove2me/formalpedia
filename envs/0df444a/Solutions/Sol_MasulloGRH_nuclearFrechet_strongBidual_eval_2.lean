-- Prove2me | solution 2 for MasulloGRH.nuclearFrechet_strongBidual_eval
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:46:49.853332+00:00
-- url     : https://prove2.me/submissions/971f950f-5d9f-4d69-9841-685d8c97ccce

import Theorems.Thm_MasulloGRH_nuclearFrechet_strongBidual_bounded_repr

set_option autoImplicit false

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : MasulloGRH.IsFrechet E) (hN : MasulloGRH.IsNuclear E)
    (F : StrongDual ℂ (StrongDual ℂ E)) :
    ∃ y : E, ∀ f : StrongDual ℂ E, F f = f y := by
  let q : Seminorm ℂ (StrongDual ℂ E) := (normSeminorm ℂ ℂ).comp F.toLinearMap
  have hq : Continuous q := continuous_norm.comp F.continuous
  obtain ⟨D, -, hD⟩ := MasulloGRH.nuclearFrechet_strongBidual_bounded_repr E hE hN q hq
  obtain ⟨y, -, hy⟩ := hD F (fun f => le_rfl)
  exact ⟨y, hy⟩
