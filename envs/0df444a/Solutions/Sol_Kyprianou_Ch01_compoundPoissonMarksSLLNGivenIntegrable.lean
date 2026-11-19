-- Prove2me | solution 1 for Kyprianou.Ch01.compoundPoissonMarksSLLNGivenIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:09:17.123593+00:00
-- url     : https://prove2.me/submissions/7d2551c8-b2d7-42e3-8c73-867bf798aecd

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_iidRealMarkStrongLawBridge
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonMarksIdentDistrib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- The source's compound-Poisson marks satisfy the IID strong law if integrable. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (arrival marks : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hIntegrable : Integrable (marks 0) Q) :
    ∀ᵐ ω ∂Q, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, marks i ω)
      atTop (𝓝 (∫ ω, marks 0 ω ∂Q)) := by
  exact Kyprianou.Ch01.iidRealMarkStrongLawBridge Q marks hIntegrable
    (by simpa only [Sum.elim_inr] using
      (hdriver.indep.precomp (g := (Sum.inr : ℕ → ℕ ⊕ ℕ)) Sum.inr_injective))
    (Kyprianou.Ch01.compoundPoissonMarksIdentDistrib
      Q arrival marks rate jumpLaw hdriver)
