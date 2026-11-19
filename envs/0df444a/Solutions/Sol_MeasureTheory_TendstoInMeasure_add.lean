-- Prove2me | solution 1 for MeasureTheory.TendstoInMeasure.add
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T02:55:53.932788+00:00
-- url     : https://prove2.me/submissions/8f8dbb0e-ce94-4f03-9415-400c4c4c6adc

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open scoped ENNReal Topology
open MeasureTheory Filter

theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {ι E : Type*} [NormedAddCommGroup E]
    {f g : ι → Ω → E} {l₁ l₂ : Ω → E} {u : Filter ι}
    (hf : TendstoInMeasure μ f u l₁) (hg : TendstoInMeasure μ g u l₂) :
    TendstoInMeasure μ (fun n ω ↦ f n ω + g n ω) u (fun ω ↦ l₁ ω + l₂ ω) := by
  intro ε hε
  have hε2 : (0 : ℝ≥0∞) < ε / 2 := ENNReal.half_pos hε.ne'
  have h_le : ∀ n, μ {ω | ε ≤ edist (f n ω + g n ω) (l₁ ω + l₂ ω)} ≤
      μ {ω | ε / 2 ≤ edist (f n ω) (l₁ ω)} + μ {ω | ε / 2 ≤ edist (g n ω) (l₂ ω)} := by
    intro n
    refine (measure_mono ?_).trans (measure_union_le _ _)
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    by_contra! h
    have htri : edist (f n ω + g n ω) (l₁ ω + l₂ ω) ≤
        edist (f n ω) (l₁ ω) + edist (g n ω) (l₂ ω) := edist_add_add_le _ _ _ _
    have hsum : edist (f n ω) (l₁ ω) + edist (g n ω) (l₂ ω) < ε / 2 + ε / 2 :=
      ENNReal.add_lt_add h.1 h.2
    rw [ENNReal.add_halves] at hsum
    exact not_lt_of_ge hω (htri.trans_lt hsum)
  have h_tend : Tendsto (fun n => μ {ω | ε / 2 ≤ edist (f n ω) (l₁ ω)} +
      μ {ω | ε / 2 ≤ edist (g n ω) (l₂ ω)}) u (𝓝 0) := by
    simpa using (hf (ε / 2) hε2).add (hg (ε / 2) hε2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_tend
    (fun _ => zero_le) h_le
