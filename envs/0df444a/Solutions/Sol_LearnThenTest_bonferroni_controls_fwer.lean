-- Prove2me | solution 1 for LearnThenTest.bonferroni_controls_fwer
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:48:06.983377+00:00
-- url     : https://prove2.me/submissions/2932bce1-ae4f-4671-aac2-176e840f1d88

import Mathlib
import Definitions.Def_LearnThenTest_Basic

open MeasureTheory ProbabilityTheory Filter
namespace LearnThenTest

theorem _root_.solution (N : ℕ) (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    IsFWERControlling N δ (bonferroni N δ) := by
  refine ⟨fun j => ?_, fun μ hμ J0 hsupp hval => ?_⟩
  · have : {x : Fin N → ℝ | j ∈ bonferroni N δ x} = {x | x j ≤ δ / N} := by
      ext x; simp [bonferroni]
    rw [this]
    exact measurableSet_le (measurable_pi_apply j) measurable_const
  · set B : Set (Fin N → ℝ) := ⋃ j ∈ J0, {x | x j ≤ δ / N} with hB
    have hBm : MeasurableSet B :=
      Finset.measurableSet_biUnion _ fun j _ => measurableSet_le (measurable_pi_apply j) measurable_const
    have hsub : Bᶜ ⊆ {x | bonferroni N δ x ⊆ J0ᶜ} := by
      intro x hx j hj
      rw [Finset.mem_compl]
      intro hj0
      apply hx
      rw [hB]
      simp only [Set.mem_iUnion]
      exact ⟨j, hj0, by simpa [bonferroni] using hj⟩
    have hμB : μ B ≤ ENNReal.ofReal δ := by
      have h1 : μ B ≤ ∑ j ∈ J0, ENNReal.ofReal (δ / N) := by
        refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
        have hN : (1:ℝ) ≤ N := by exact_mod_cast (Nat.one_le_of_lt j.2)
        by_cases h1 : δ / N ≤ 1
        · exact hval j hj (δ / N) ⟨div_nonneg hδ.1.le (by positivity), h1⟩
        · exact absurd (by rw [div_le_one (by linarith)]; linarith [hδ.2]) h1
      refine h1.trans ?_
      rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hc : (J0.card : ℝ) ≤ N := by exact_mod_cast (le_trans (Finset.card_le_univ J0) (by simp))
      rcases Nat.eq_zero_or_pos N with h | h
      · subst h; simp; exact hδ.1.le
      · have : (0:ℝ) < N := by exact_mod_cast h
        rw [mul_div_assoc', div_le_iff₀ this]
        nlinarith [hδ.1]
    refine le_trans ?_ (measure_mono hsub)
    rw [prob_compl_eq_one_sub hBm, ENNReal.ofReal_sub _ hδ.1.le, ENNReal.ofReal_one]
    exact tsub_le_tsub_left hμB 1


end LearnThenTest
