-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.exists_tendsto_of_local_holder
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T09:39:19.713563+00:00
-- url     : https://prove2.me/submissions/d3a693a0-474b-42ef-93d5-98fdcd980fee

import Definitions.Def_LevyStochCalc_Brownian_ContinuityKolmogorovBounds_F000

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


theorem _root_.solution {A : Set ℝ} (hA : Dense A) {f : ℝ → ℝ}
    {α : ℝ} (hα : 0 < α) (t : ℝ)
    (hloc : ∃ K ρ : ℝ, 0 < ρ ∧ 0 ≤ K ∧ ∀ s ∈ A, ∀ s' ∈ A,
      s ∈ Set.Ioo (t - ρ) (t + ρ) → s' ∈ Set.Ioo (t - ρ) (t + ρ) →
        |f s - f s'| ≤ K * |s - s'| ^ α) :
    ∃ y, Filter.Tendsto f (𝓝[A] t) (nhds y) := by
  obtain ⟨K, ρ, hρ, hK, hf⟩ := hloc
  haveI : (𝓝[A] t).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hA.closure_eq ▸ Set.mem_univ t)
  apply cauchy_map_iff_exists_tendsto.mp
  rw [Metric.cauchy_iff]
  refine ⟨Filter.map_neBot, fun ε hε => ?_⟩
  set c := ε / (K + 1) with hc
  have hcpos : 0 < c := div_pos hε (by linarith)
  set δ := min ρ ((c ^ (1 / α)) / 2) with hδ
  have hδpos : 0 < δ := lt_min hρ (by positivity)
  have hδρ : δ ≤ ρ := min_le_left _ _
  have h2δ : (2 * δ) ^ α ≤ c := by
    have : 2 * δ ≤ c ^ (1 / α) := by
      have := min_le_right ρ ((c ^ (1 / α)) / 2); linarith
    calc (2 * δ) ^ α ≤ (c ^ (1 / α)) ^ α := Real.rpow_le_rpow (by linarith) this hα.le
      _ = c := by rw [← Real.rpow_mul hcpos.le, one_div_mul_cancel hα.ne', Real.rpow_one]
  refine ⟨f '' (A ∩ Set.Ioo (t - δ) (t + δ)), ?_, ?_⟩
  · rw [Filter.mem_map]
    apply Filter.mem_of_superset (inter_mem_nhdsWithin A (Ioo_mem_nhds (a := t - δ) (b := t + δ) (by linarith) (by linarith)))
    intro s hs
    exact ⟨s, ⟨hs.1, hs.2⟩, rfl⟩
  · rintro _ ⟨s, ⟨hsA, hs⟩, rfl⟩ _ ⟨s', ⟨hs'A, hs'⟩, rfl⟩
    have h1 : s ∈ Set.Ioo (t - ρ) (t + ρ) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h2 : s' ∈ Set.Ioo (t - ρ) (t + ρ) := ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
    have hss : |s - s'| ≤ 2 * δ := by
      rw [abs_le]; constructor <;> linarith [hs.1, hs.2, hs'.1, hs'.2]
    have hpow : |s - s'| ^ α ≤ c := (Real.rpow_le_rpow (abs_nonneg _) hss hα.le).trans h2δ
    rw [Real.dist_eq]
    calc |f s - f s'| ≤ K * |s - s'| ^ α := hf s hsA s' hs'A h1 h2
      _ ≤ K * c := mul_le_mul_of_nonneg_left hpow hK
      _ < ε := by
        rw [hc, mul_div_assoc']
        rw [div_lt_iff₀ (by linarith)]
        nlinarith

end LevyStochCalc.Brownian.Continuity
