-- Prove2me | solution 1 for MasulloRepair.L2_kernel_composition_nuclear
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T20:09:01.965033+00:00
-- url     : https://prove2.me/submissions/a3b78620-560b-44ad-8d97-294114cf7149

import Theorems.Thm_MasulloRepair_hilbertSchmidt_comp_nuclear
import Theorems.Thm_MasulloGRH_trace_formula_integral_operators
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open MasulloGRH MasulloRepair MeasureTheory ContinuousLinearMap

theorem solution {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [μ.Regular] [SigmaFinite μ] (k l : X → X → ℂ)
    (hk : MemLp (fun p : X × X => k p.1 p.2) 2 (μ.prod μ))
    (hl : MemLp (fun p : X × X => l p.1 p.2) 2 (μ.prod μ)) :
    ∃ T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ,
      (∀ u : Lp ℂ 2 μ, ∀ᵐ x ∂μ,
        T u x = ∫ z, k x z * (∫ y, l z y * u y ∂μ) ∂μ) ∧
      IsNuclearOperator T ∧
      traceNorm T ≤ (eLpNorm (fun p : X × X => k p.1 p.2) 2 (μ.prod μ)).toReal *
        (eLpNorm (fun p : X × X => l p.1 p.2) 2 (μ.prod μ)).toReal := by
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  obtain ⟨A, hAk, hA, hAnorm, _⟩ := trace_formula_integral_operators μ k hk
  obtain ⟨B, hBl, hB, hBnorm, _⟩ := trace_formula_integral_operators μ l hl
  obtain ⟨hnuc, hnorm⟩ := hilbertSchmidt_comp_nuclear A B hA hB
  refine ⟨A ∘L B, ?_, hnuc, ?_⟩
  · intro u
    filter_upwards [hAk (B u)] with x hx
    change A (B u) x = _
    rw [hx]
    apply integral_congr_ae
    filter_upwards [hBl u] with z hz
    rw [hz]
  · simpa only [hAnorm, hBnorm] using hnorm

#print axioms solution
