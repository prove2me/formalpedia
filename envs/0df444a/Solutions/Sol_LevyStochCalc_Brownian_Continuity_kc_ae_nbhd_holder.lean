-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.kc_ae_nbhd_holder
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T09:49:09.885062+00:00
-- url     : https://prove2.me/submissions/74c9945f-e69a-48d7-8634-a67542941e28

import Definitions.Def_LevyStochCalc_Brownian_ContinuityKolmogorovBounds_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Almost-sure Hölder bounds from the Kolmogorov condition

The probabilistic half of the Kolmogorov-Chentsov construction. For a process `X` with
`∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤ M · edist s t ^ q`, Markov's inequality bounds each
increment tail by `M · edist s t ^ q / lam ^ p`; summing over the `2^n` level-`n` dyadic
intervals of `[0, 1]` makes the bad sets `{|increment| > ((1/2)^α)^n}` summable whenever
`α * p < q - 1`, so Borel-Cantelli gives an almost-sure bound on all small-scale dyadic
increments. Feeding those bounds to the deterministic chaining yields almost-sure local
`α`-Hölder continuity on the dyadics, and the convergence-in-measure form of the same tail
bound identifies the dyadic extension as a modification of `X`
(`kolmogorov_modification_ae_eq`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Continuity

universe u

variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.solution
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    {α : ℝ} (hα0 : 0 < α) (hαpq : α * p < q - 1) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, ∃ K ρ : ℝ, 0 < ρ ∧ 0 ≤ K ∧ ∀ s ∈ dyadicRationals,
      ∀ s' ∈ dyadicRationals, s ∈ Set.Ioo (t - ρ) (t + ρ) →
        s' ∈ Set.Ioo (t - ρ) (t + ρ) → |X s ω - X s' ω| ≤ K * |s - s'| ^ α := by
  filter_upwards [kc_ae_interval_holder P X hX hα0 hαpq] with ω hω
  intro t
  choose K N hK0 hKb using hω
  set j0 : ℤ := ⌊t⌋ with hj0
  set S : Finset ℤ := Finset.Icc (j0 - 2) (j0 + 2) with hS
  set Ks : ℝ := ∑ j ∈ S, K j with hKs
  set Nm : ℕ := S.sup N with hNm
  have hKs0 : 0 ≤ Ks := Finset.sum_nonneg fun i _ => hK0 i
  have hKle : ∀ j ∈ S, K j ≤ Ks := fun j hj => Finset.single_le_sum (fun i _ => hK0 i) hj
  have hNle : ∀ j ∈ S, (1 / 2 : ℝ) ^ Nm ≤ (1 / 2) ^ (N j) := fun j hj =>
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Finset.le_sup (f := N) hj)
  have hNm1 : (1 / 2 : ℝ) ^ Nm ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hρe : (1 / 2 : ℝ) ^ (Nm + 1) = (1 / 2) ^ Nm / 2 := by rw [pow_succ]; ring
  have hint : ∀ m : ℤ, (m : ℝ) ∈ dyadicRationals := fun m => ⟨m, 0, by simp⟩
  have same : ∀ a ∈ S, ∀ s ∈ dyadicRationals, ∀ s' ∈ dyadicRationals,
      (a : ℝ) ≤ s → s ≤ a + 1 → (a : ℝ) ≤ s' → s' ≤ a + 1 → |s - s'| ≤ (1 / 2 : ℝ) ^ Nm →
      |X s ω - X s' ω| ≤ Ks * |s - s'| ^ α := by
    intro a ha s hs s' hs' h1 h2 h3 h4 h5
    calc |X s ω - X s' ω| ≤ K a * |s - s'| ^ α :=
          hKb a s hs s' hs' h1 h2 h3 h4 (h5.trans (hNle a ha))
      _ ≤ Ks * |s - s'| ^ α := mul_le_mul_of_nonneg_right (hKle a ha) (by positivity)
  have ht1 : (j0 : ℝ) ≤ t := Int.floor_le t
  have ht2 : t < (j0 : ℝ) + 1 := Int.lt_floor_add_one t
  have main : ∀ s ∈ dyadicRationals, ∀ s' ∈ dyadicRationals,
      s ∈ Set.Ioo (t - (1 / 2) ^ (Nm + 1)) (t + (1 / 2) ^ (Nm + 1)) →
      s' ∈ Set.Ioo (t - (1 / 2) ^ (Nm + 1)) (t + (1 / 2) ^ (Nm + 1)) → s ≤ s' →
      |X s ω - X s' ω| ≤ 2 * Ks * |s - s'| ^ α := by
    intro s hs s' hs' hsw hs'w hss
    rw [hρe] at hsw hs'w
    obtain ⟨hsw1, hsw2⟩ := hsw
    obtain ⟨hs'w1, hs'w2⟩ := hs'w
    set a : ℤ := ⌊s⌋ with ha
    have ha1 : (a : ℝ) ≤ s := Int.floor_le s
    have ha2 : s < (a : ℝ) + 1 := Int.lt_floor_add_one s
    have haS1 : j0 - 1 ≤ a := by
      rw [ha, Int.le_floor]; push_cast; linarith
    have haS2 : a ≤ j0 + 1 := by
      have : a < j0 + 2 := by
        rw [ha, Int.floor_lt]; push_cast; linarith
      omega
    have haS : a ∈ S := by rw [hS, Finset.mem_Icc]; omega
    have ha1S : a + 1 ∈ S := by rw [hS, Finset.mem_Icc]; omega
    have hdist : |s - s'| ≤ (1 / 2 : ℝ) ^ Nm := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    have hpos : 0 ≤ Ks * |s - s'| ^ α := by positivity
    by_cases hc : s' ≤ (a : ℝ) + 1
    · have := same a haS s hs s' hs' ha1 ha2.le (by linarith) hc hdist
      linarith
    · push_neg at hc
      have hm := hint (a + 1)
      push_cast at hm
      have hs'2 : s' ≤ ((a + 1 : ℤ) : ℝ) + 1 := by push_cast; linarith
      have d1 : |s - ((a : ℝ) + 1)| ≤ |s - s'| := by
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
      have d2 : |((a : ℝ) + 1) - s'| ≤ |s - s'| := by
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
      have e1 := same a haS s hs _ hm ha1 ha2.le (by linarith) le_rfl (d1.trans hdist)
      have e2 := same (a + 1) ha1S _ hm s' hs' (by push_cast; linarith) (by push_cast; linarith)
        (by push_cast; linarith) hs'2 (d2.trans hdist)
      have p1 : |s - ((a : ℝ) + 1)| ^ α ≤ |s - s'| ^ α :=
        Real.rpow_le_rpow (abs_nonneg _) d1 hα0.le
      have p2 : |((a : ℝ) + 1) - s'| ^ α ≤ |s - s'| ^ α :=
        Real.rpow_le_rpow (abs_nonneg _) d2 hα0.le
      have q1 := mul_le_mul_of_nonneg_left p1 hKs0
      have q2 := mul_le_mul_of_nonneg_left p2 hKs0
      have tri : |X s ω - X s' ω| ≤ |X s ω - X ((a : ℝ) + 1) ω| + |X ((a : ℝ) + 1) ω - X s' ω| :=
        abs_sub_le _ _ _
      linarith
  refine ⟨2 * Ks, (1 / 2) ^ (Nm + 1), by positivity, by positivity, ?_⟩
  intro s hs s' hs' hsw hs'w
  rcases le_total s s' with h | h
  · exact main s hs s' hs' hsw hs'w h
  · rw [abs_sub_comm (X s ω), abs_sub_comm s]
    exact main s' hs' s hs hs'w hsw h

end LevyStochCalc.Brownian.Continuity
