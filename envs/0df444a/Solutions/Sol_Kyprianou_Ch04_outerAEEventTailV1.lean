-- Prove2me | solution 1 for Kyprianou.Ch04.outerAEEventTailV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:03:47.101585+00:00
-- url     : https://prove2.me/submissions/5771434a-cdf3-4902-8a04-5d3f97e26c2c

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal Topology
set_option autoImplicit false

/-- A sequence of measurable event envelopes that eventually excludes almost every
sample has vanishing outer probabilities, including for arbitrary subsets. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A B : ℕ → Set Ω)
    (hB : ∀ n, MeasurableSet (B n))
    (hSub : ∀ n, ∀ᵐ w ∂P, w ∈ A n → w ∈ B n)
    (hAE : ∀ᵐ w ∂P, ∃ N : ℕ, ∀ n ≥ N, w ∉ B n) :
    Tendsto (fun n => (P (A n)).toReal) atTop (nhds 0) := by
  let C : ℕ → Set Ω := fun n => ⋃ k : ℕ, B (n+k)
  have hC (n : ℕ) : MeasurableSet (C n) := MeasurableSet.iUnion (fun k => hB (n+k))
  have hcAnti : Antitone C := by
    intro i j hij w hw
    obtain ⟨k,hk⟩ := mem_iUnion.mp hw
    apply mem_iUnion.mpr
    refine ⟨j-i+k,?_⟩
    have he : i+(j-i+k)=j+k := by omega
    simpa only [he] using hk
  have hNull : P (⋂ n, C n) = 0 := by
    apply le_antisymm ?_ (by positivity)
    rw [← measure_empty (μ := P)]
    apply measure_mono_ae
    filter_upwards [hAE] with w hw hmem
    obtain ⟨N,hN⟩ := hw
    obtain ⟨k,hk⟩ := mem_iUnion.mp (mem_iInter.mp hmem N)
    exact (hN (N+k) (by omega) hk).elim
  have hlim := tendsto_measure_iInter_atTop (μ := P)
    (fun n => (hC n).nullMeasurableSet) hcAnti ⟨0,measure_ne_top P _⟩
  rw [hNull] at hlim
  have hreal := (ENNReal.tendsto_toReal_zero_iff
    (fun n => measure_ne_top P (C n))).mpr hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hreal
  · intro n; exact ENNReal.toReal_nonneg
  · intro n
    apply ENNReal.toReal_mono (measure_ne_top P _)
    apply (measure_mono_ae (hSub n)).trans
    apply measure_mono
    intro w hw
    change w ∈ ⋃ k : ℕ, B (n+k)
    apply mem_iUnion.mpr
    refine ⟨0,?_⟩
    change w ∈ B (n+0)
    rw [Nat.add_zero]
    exact hw
