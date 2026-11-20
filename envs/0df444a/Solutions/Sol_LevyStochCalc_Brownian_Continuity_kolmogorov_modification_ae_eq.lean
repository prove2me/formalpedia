-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.kolmogorov_modification_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T09:42:35.718113+00:00
-- url     : https://prove2.me/submissions/a6c27f12-f002-4d66-8808-c2c86361c73c

import Definitions.Def_LevyStochCalc_Brownian_ContinuityDyadicChaining_F001

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
    (Y : ℝ → Ω → ℝ)
    (h_continuous : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω))
    (h_dyadic_eq : ∀ s ∈ dyadicRationals, ∀ᵐ ω ∂P, Y s ω = X s ω) :
    ∀ t : ℝ, ∀ᵐ ω ∂P, Y t ω = X t ω := by
  intro t
  obtain ⟨u, -, hu, hut⟩ := exists_seq_dyadic_tendsto t
  have hp := hX.p_pos
  have hq := hX.q_pos
  have hTM : TendstoInMeasure P (fun n => X (u n)) Filter.atTop (X t) := by
    refine tendstoInMeasure_of_ne_top fun ε hε hεt => ?_
    have hεp0 : ε ^ p ≠ 0 := by
      rw [Ne, ENNReal.rpow_eq_zero_iff]; push_neg
      exact ⟨fun h => absurd h hε.ne', fun _ => hp.le⟩
    have hεpt : ε ^ p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp.le hεt
    have hbound : ∀ n, P {ω | ε ≤ edist (X (u n) ω) (X t ω)} ≤
        (M : ℝ≥0∞) * edist (u n) t ^ q / ε ^ p := by
      intro n
      calc P {ω | ε ≤ edist (X (u n) ω) (X t ω)}
          ≤ P {ω | ε ^ p ≤ edist (X (u n) ω) (X t ω) ^ p} := by
            apply measure_mono
            intro ω hω
            exact ENNReal.rpow_le_rpow hω hp.le
        _ ≤ (∫⁻ ω, edist (X (u n) ω) (X t ω) ^ p ∂P) / ε ^ p :=
            meas_ge_le_lintegral_div
              ((hX.measurable_edist).pow_const p).aemeasurable hεp0 hεpt
        _ ≤ (M : ℝ≥0∞) * edist (u n) t ^ q / ε ^ p := by
            gcongr
            exact hX.kolmogorovCondition (u n) t
    have hlim : Filter.Tendsto (fun n => (M : ℝ≥0∞) * edist (u n) t ^ q / ε ^ p)
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n => edist (u n) t) Filter.atTop (nhds 0) :=
        (tendsto_iff_edist_tendsto_0).mp hut
      have h2 : Filter.Tendsto (fun n => edist (u n) t ^ q) Filter.atTop (nhds 0) := by
        have := (ENNReal.continuous_rpow_const (y := q)).tendsto 0
        rw [ENNReal.zero_rpow_of_pos hq] at this
        exact this.comp h1
      have h3 := ENNReal.Tendsto.const_mul h2 (Or.inr ENNReal.coe_ne_top) (a := (M : ℝ≥0∞))
      rw [mul_zero] at h3
      have h4 := ENNReal.Tendsto.div_const h3 (Or.inr hεp0)
      rwa [ENNReal.zero_div] at h4
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => zero_le) hbound
  obtain ⟨ns, hnsm, hns⟩ := hTM.exists_seq_tendsto_ae
  have hall : ∀ᵐ ω ∂P, ∀ n, Y (u n) ω = X (u n) ω :=
    ae_all_iff.mpr fun n => h_dyadic_eq (u n) (hu n).2
  filter_upwards [hns, hall, h_continuous] with ω hω hω2 hω3
  have hY : Filter.Tendsto (fun i => Y (u (ns i)) ω) Filter.atTop (nhds (Y t ω)) :=
    (hω3.tendsto t).comp (hut.comp hnsm.tendsto_atTop)
  have hY' : Filter.Tendsto (fun i => X (u (ns i)) ω) Filter.atTop (nhds (Y t ω)) := by
    simpa only [hω2] using hY
  exact tendsto_nhds_unique hY' hω

end LevyStochCalc.Brownian.Continuity
