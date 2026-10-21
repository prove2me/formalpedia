-- Prove2me | solution 1 for ImprovedMMS.Additive.observation_3_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:47:42.258848+00:00
-- url     : https://prove2.me/submissions/682f5e77-6334-401f-999e-3c267303c927

import Mathlib
import Definitions.Def_ImprovedMMS_Additive_Envy

set_option autoImplicit false
open ImprovedMMS.Additive

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (f g : Fin n → Finset (Fin m))
    (C : Finset (Fin n)) (hC : ∀ i ∈ C, IsSemiSatisfied f g i) (hcef : IsCycleEnvyFree v f C)
    (pos : Fin n → ℕ) (hpos : IsTopologicalOrder v f C pos) :
    ∀ i ∈ C, ∀ j ∈ C, pos j < pos i → v i (f j) ≤ 3 / 4 - eps v f i := by
  intro i hi j hj hlt
  have hne : i ≠ j := fun h => by subst h; omega
  have hn : ¬ envies v f i j := fun he => by
    have := hpos.2 i hi j hj ⟨hi, hj, he⟩
    omega
  unfold envies at hn
  push_neg at hn
  have := hn hne
  unfold eps
  linarith
