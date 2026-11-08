-- Prove2me | solution 1 for GoodProphets.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:23:06.381113+00:00
-- url     : https://prove2.me/submissions/4d9fe7bb-55e6-4db2-b7b2-2f0e87ced27a

import Mathlib
import Definitions.Def_GoodProphets_lpObj

open GoodProphets in
theorem solution {k ℓ r m : ℕ} (I : Instance k ℓ r m) (N : Fin k → ℝ)
    (y y' xstar : Fin k → Fin ℓ → ℝ) (hyy' : ∀ θ j, y θ j ≤ y' θ j)
    (hopt : IsOptIn I N y xstar) (hle : ∀ θ j, y' θ j ≤ xstar θ j) :
    optVal I N y' = optVal I N y := by
  have hx' : xstar ∈ Feas N y' := ⟨hle, hopt.1.2⟩
  have h1 : IsLeast (lpObj I N '' Feas N y) (lpObj I N xstar) := by
    refine ⟨⟨xstar, hopt.1, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hopt.2 x hx
  have h2 : IsLeast (lpObj I N '' Feas N y') (lpObj I N xstar) := by
    refine ⟨⟨xstar, hx', rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hopt.2 x ⟨fun θ j => (hyy' θ j).trans (hx.1 θ j), hx.2⟩
  unfold optVal
  rw [h1.csInf_eq, h2.csInf_eq]
