-- Prove2me | solution 1 for GradErrors.Deterministic.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T00:15:42.467585+00:00
-- url     : https://prove2.me/submissions/1a2b83a5-8792-47c8-9128-0a40d1c5850b

import Mathlib

open Filter Topology NNReal InnerProductSpace


namespace GradErrors.Deterministic

theorem lemma_1_core (Y W Z : ℕ → ℝ) (hW : ∀ t, 0 ≤ W t)
    (hrec : ∀ t, Y (t + 1) ≤ Y t - W t + Z t)
    (hZ : ∃ S : ℝ, Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), Z t) atTop (𝓝 S)) :
    Tendsto Y atTop atBot ∨ ((∃ y : ℝ, Tendsto Y atTop (𝓝 y)) ∧ Summable W) := by
  obtain ⟨S, hS⟩ := hZ
  set P : ℕ → ℝ := fun T => ∑ t ∈ Finset.range T, Z t with hP
  have hPS : Tendsto P atTop (𝓝 S) := (tendsto_add_atTop_iff_nat 1).mp hS
  set V : ℕ → ℝ := fun t => Y t - P t with hV
  have hVs : ∀ t, V (t + 1) ≤ V t - W t := by
    intro t
    simp only [hV, hP, Finset.sum_range_succ]
    linarith [hrec t]
  have hanti : Antitone V := antitone_nat_of_succ_le (fun t => by linarith [hVs t, hW t])
  have hYV : Y = fun t => V t + P t := by funext t; simp [hV]
  by_cases hb : BddBelow (Set.range V)
  · right
    obtain ⟨b, hb'⟩ := hb
    have hVb : ∀ t, b ≤ V t := fun t => hb' ⟨t, rfl⟩
    refine ⟨⟨(⨅ i, V i) + S, ?_⟩, ?_⟩
    · rw [hYV]
      exact (tendsto_atTop_ciInf hanti ⟨b, hb'⟩).add hPS
    · apply summable_of_sum_range_le hW (c := V 0 - b)
      intro N
      have : ∑ t ∈ Finset.range N, W t ≤ V 0 - V N := by
        induction N with
        | zero => simp
        | succ N ih => rw [Finset.sum_range_succ]; linarith [hVs N]
      linarith [hVb N]
  · left
    have hVbot : Tendsto V atTop atBot := by
      rw [tendsto_atTop_atBot]
      intro b
      have : ∃ N, V N < b := by
        by_contra hc
        push Not at hc
        exact hb ⟨b, by rintro _ ⟨t, rfl⟩; exact hc t⟩
      obtain ⟨N, hN⟩ := this
      exact ⟨N, fun t ht => (hanti ht).trans hN.le⟩
    rw [hYV]
    exact hVbot.atBot_add hPS

end GradErrors.Deterministic

open GradErrors.Deterministic


theorem solution (Y W Z : ℕ → ℝ) (hW : ∀ t, 0 ≤ W t)
    (hrec : ∀ t, Y (t + 1) ≤ Y t - W t + Z t)
    (hZ : ∃ S : ℝ, Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), Z t) atTop (𝓝 S)) :
    Tendsto Y atTop atBot ∨ ((∃ y : ℝ, Tendsto Y atTop (𝓝 y)) ∧ Summable W) := by
  exact lemma_1_core Y W Z hW hrec hZ
