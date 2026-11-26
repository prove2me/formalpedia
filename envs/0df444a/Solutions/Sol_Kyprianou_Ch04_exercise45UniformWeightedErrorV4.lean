-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45UniformWeightedErrorV4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:38:31.070642+00:00
-- url     : https://prove2.me/submissions/3f215e7c-bbab-40c0-b172-1aa51098b3fe

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false
theorem solution
    {ι : Type} (S : Finset ι) (T : NNReal)
    (D : ℕ → NNReal → ℝ) (d : NNReal → ℝ)
    (J : ι → ℕ → NNReal → ℝ) (j : ι → NNReal → ℝ)
    (b : ℝ) (a : ι → ℝ)
    (hD : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ T, |D n t - d t| < δ)
    (hJ : ∀ r ∈ S, ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ T,
      |J r n t - j r t| < δ) :
    ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ T,
      |(b * D n t + ∑ r ∈ S, a r * J r n t) -
        (b * d t + ∑ r ∈ S, a r * j r t)| < δ := by
  intro δ hδ
  let C : ℝ := |b| + (∑ r ∈ S, |a r|) + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  let ε := δ / C
  have he : 0 < ε := div_pos hδ hC
  have hde : ∀ᶠ n : ℕ in atTop, ∀ t ≤ T, |D n t-d t| < ε :=
    eventually_atTop.2 (hD ε he)
  have hje : ∀ᶠ n : ℕ in atTop, ∀ r ∈ S, ∀ t ≤ T, |J r n t-j r t| < ε :=
    (eventually_all_finset S).2 (fun r hr => eventually_atTop.2 (hJ r hr ε he))
  apply eventually_atTop.1
  filter_upwards [hde,hje] with n hn hnj t ht
  have hrew : (b * D n t + ∑ r ∈ S, a r * J r n t) -
      (b * d t + ∑ r ∈ S, a r * j r t) =
      b * (D n t-d t) + ∑ r ∈ S, a r * (J r n t-j r t) := by
    simp only [mul_sub,Finset.sum_sub_distrib]
    ring
  rw [hrew]
  calc
    _ ≤ |b * (D n t-d t)| + |∑ r ∈ S, a r * (J r n t-j r t)| := abs_add_le _ _
    _ ≤ |b| * ε + ∑ r ∈ S, |a r| * ε := by
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hn t ht).le (abs_nonneg b)
      · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
        intro r hr
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hnj r hr t ht).le (abs_nonneg _)
    _ = (C-1)*ε := by rw [← Finset.sum_mul]; dsimp [C]; ring
    _ < δ := by
      have hh : C * ε = δ := by dsimp [ε]; field_simp
      nlinarith