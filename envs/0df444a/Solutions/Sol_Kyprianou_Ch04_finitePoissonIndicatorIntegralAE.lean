-- Prove2me | solution 1 for Kyprianou.Ch04.finitePoissonIndicatorIntegralAE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:25:38.298576+00:00
-- url     : https://prove2.me/submissions/a2c19d05-81e0-42d3-a69a-8c8fa4928c28

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch04_finiteWeightedIndicatorIntegral
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped ENNReal NNReal BigOperators
set_option autoImplicit false
universe u v w

/-- The physical compensated integral of a finite weighted indicator sum. -/
theorem solution
    {Ω : Type u} {E : Type v} {ι : Type w}
    [MeasurableSpace Ω] [MeasurableSpace E] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure E) [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν)
    (s : Finset ι) (B : ι → Set (ℝ × E)) (H : ι → Ω → ℝ)
    (hB : ∀ i ∈ s, MeasurableSet (B i))
    (hFin : ∀ i ∈ s, referenceIntensity ν (B i) ≠ ⊤) :
    let K := fun ω z => ∑ i ∈ s, (B i).indicator (fun _ => H i ω) z
    ∀ᵐ ω ∂P, (∫ z, K ω z ∂(N.N ω)) -
      (∫ z, K ω z ∂referenceIntensity ν) =
      ∑ i ∈ s, H i ω * N.compensated (B i) ω := by
  dsimp only
  have hN : ∀ᵐ ω ∂P, ∀ i ∈ s, N.N ω (B i) ≠ ⊤ := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      have h1 := N.integer_valued (hB i (Finset.mem_insert_self i s))
        (hFin i (Finset.mem_insert_self i s))
      have h2 := ih (fun j hj => hB j (Finset.mem_insert_of_mem hj))
        (fun j hj => hFin j (Finset.mem_insert_of_mem hj))
      filter_upwards [h1,h2] with ω hw hws
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · obtain ⟨n, hn⟩ := hw
        rw [hn]
        exact ENNReal.natCast_ne_top n
      · exact hws j hj
  filter_upwards [hN] with ω hw
  rw [(Kyprianou.Ch04.finiteWeightedIndicatorIntegral (N.N ω) s B
    (fun i => H i ω) hB hw).2,
    (Kyprianou.Ch04.finiteWeightedIndicatorIntegral (referenceIntensity ν) s B
    (fun i => H i ω) hB hFin).2, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [PoissonRandomMeasure.compensated, mul_sub]
