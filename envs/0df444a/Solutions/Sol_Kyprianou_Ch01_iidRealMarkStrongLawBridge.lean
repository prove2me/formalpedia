-- Prove2me | solution 1 for Kyprianou.Ch01.iidRealMarkStrongLawBridge
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T15:03:16.023511+00:00
-- url     : https://prove2.me/submissions/5f4041ff-4c72-4244-ab06-100292ec4ed9

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (marks : ℕ → Ω → ℝ)
    (hIntegrable : Integrable (marks 0) P)
    (hIndependent : iIndepFun marks P)
    (hIdent : ∀ i : ℕ, IdentDistrib (marks i) (marks 0) P P) :
    ∀ᵐ ω ∂P,
      Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, marks i ω)
        atTop (𝓝 (∫ ω, marks 0 ω ∂P)) := by
  have h := strong_law_ae marks hIntegrable
    (fun i j hij => hIndependent.indepFun hij) hIdent
  filter_upwards [h] with ω hω
  simpa [smul_eq_mul] using hω
