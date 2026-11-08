-- Prove2me | solution 1 for LowRankIndicator.R_subset_Q
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:51:19.615476+00:00
-- url     : https://prove2.me/submissions/ce3e508e-e2c2-409f-9491-cd83d6a2e485

import Mathlib
import Definitions.Def_LowRankIndicator_Sets

open LowRankIndicator in
theorem solution {n k : ℕ} (g : (Fin k → ℝ) → EReal) (A : Matrix (Fin k) (Fin n) ℝ)
    (c : Fin n → ℝ) (Iplus : Set (Fin n)) (hf : LowRankIndicator.objective g A c 0 = 0) :
    LowRankIndicator.R A c Iplus ⊆ LowRankIndicator.Q g A c Iplus := by
  rintro ⟨t, x, z⟩ ⟨h1, h2, h3, h4⟩
  change c ⬝ᵥ x ≤ t at h1
  change A.mulVec x = 0 at h2
  change ∀ i ∈ Iplus, 0 ≤ x i at h3
  change ∀ i, z i = 1 at h4
  have hg : g 0 = 0 := by
    unfold LowRankIndicator.objective at hf
    simpa [Matrix.mulVec_zero, dotProduct_zero] using hf
  refine ⟨?_, h3, fun i => Or.inr (h4 i), fun i => by simp [h4 i]⟩
  change LowRankIndicator.objective g A c x ≤ (t : EReal)
  unfold LowRankIndicator.objective
  rw [h2, hg, zero_add]
  exact_mod_cast h1
