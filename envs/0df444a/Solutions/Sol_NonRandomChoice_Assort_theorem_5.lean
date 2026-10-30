-- Prove2me | solution 1 for NonRandomChoice.Assort.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T04:10:43.453077+00:00
-- url     : https://prove2.me/submissions/e5f38d01-f834-451f-9c5f-e535deb0e955

import Mathlib
import Definitions.Def_NonRandomChoice_Assort_Model
import Definitions.Def_RevenueOrdered_Ratio_Model
import Theorems.Thm_NonRandomChoice_Assort_lemma_1
import Theorems.Thm_NonRandomChoice_Assort_model_satisfies_lemma_1

open NonRandomChoice.Assort in
theorem solution {N : ℕ} (μ u0 : ℝ) (hμ : 0 < μ) (u : Fin N → ℝ) (ip : Fin N)
    (p : Fin N → ℝ) (hp : Antitone p) (hp0 : ∀ i, 0 ≤ p i) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ N ∧ ∀ S : Finset (Fin N),
      revenue12 μ u0 u ip p S ≤ revenue12 μ u0 u ip p (roSet N n) := by
  obtain ⟨hreg, ⟨f, D, hc, hnn, hrep⟩, hrev⟩ := model_satisfies_lemma_1 μ u0 hμ u ip
  obtain ⟨n, hnN, hopt⟩ := lemma_1 (choiceProb μ u0 u ip) hreg p hp f D hc hnn hrep
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (fun h => by subst h; exact ip.elim0)
  simp only [hrev]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, le_rfl, hN, fun S => (hopt S).trans ?_⟩
    have h0 : roSet N 0 = ∅ := by ext i; simp [roSet]
    rw [h0]
    simp only [RevenueOrdered.Ratio.revenue, Finset.sum_empty]
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (hreg.nonneg x _) (hp0 x))
  · exact ⟨n, hn, hnN, hopt⟩
