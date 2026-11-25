-- Prove2me | solution 1 for Kyprianou.Ch04.compensatedDisjointUnionAE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:54:38.352046+00:00
-- url     : https://prove2.me/submissions/343065ca-c215-41bf-8cce-ee19e7e52954

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped ENNReal NNReal
set_option autoImplicit false
universe u v

/-- Compensated counts add almost surely on disjoint finite-intensity sets. -/
theorem solution
    {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν] (N : PoissonRandomMeasure P ν)
    {A B : Set (ℝ × E)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hd : Disjoint A B)
    (hAfin : referenceIntensity ν A ≠ ⊤)
    (hBfin : referenceIntensity ν B ≠ ⊤) :
    (fun ω => N.compensated (A ∪ B) ω) =ᵐ[P]
      (fun ω => N.compensated A ω + N.compensated B ω) := by
  filter_upwards [N.integer_valued hA hAfin, N.integer_valued hB hBfin]
    with ω ha hb
  obtain ⟨n, hn⟩ := ha
  obtain ⟨m, hm⟩ := hb
  have ha' : N.N ω A ≠ ⊤ := by rw [hn]; exact ENNReal.natCast_ne_top n
  have hb' : N.N ω B ≠ ⊤ := by rw [hm]; exact ENNReal.natCast_ne_top m
  simp only [PoissonRandomMeasure.compensated, measure_union hd hB,
    ENNReal.toReal_add ha' hb', ENNReal.toReal_add hAfin hBfin]
  ring
