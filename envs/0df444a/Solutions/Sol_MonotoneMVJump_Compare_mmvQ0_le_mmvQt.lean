-- Prove2me | solution 1 for MonotoneMVJump.Compare.mmvQ0_le_mmvQt
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T09:51:54.386685+00:00
-- url     : https://prove2.me/submissions/e7af9d50-0fa4-498a-aaf5-b05473f395ab

import Mathlib
import Definitions.Def_MonotoneMVJump_Compare_PDE

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

open MonotoneMVJump.Compare

theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω)
    (hP : IsProbabilityMeasure M.P) (t : ℝ≥0) (θ : ℝ) (X : Ω → ℝ) :
    M.mmvQ0 θ X ≤ M.mmvQt t θ X := by
  unfold Market.mmvQt
  refine le_iInf fun η₁ => le_iInf fun η₂ => le_iInf fun ϕ => le_iInf fun E => le_iInf fun hE => ?_
  obtain ⟨-, -, -, -, h2, h1, h0⟩ := hE
  set μ := M.P with hμ
  have hEi : Integrable (E M.T) μ := Integrable.of_integral_ne_zero (by rw [h1]; exact one_ne_zero)
  have hEm : AEMeasurable (fun ω => ENNReal.ofReal (E M.T ω)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable hEi.aestronglyMeasurable.aemeasurable
  have hQp : IsProbabilityMeasure (M.Qm E) := by
    constructor
    rw [Market.Qm, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hEi h0, h1, ENNReal.ofReal_one]
  have hQP : M.Qm E ≪ μ := withDensity_absolutelyContinuous _ _
  have hrn := Measure.rnDeriv_withDensity₀ μ hEm
  have hL : ∫⁻ ω, (M.Qm E).rnDeriv μ ω ^ 2 ∂μ = ∫⁻ ω, ENNReal.ofReal (E M.T ω ^ 2) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hrn, h0] with ω hω h0
    rw [Market.Qm, hω, ENNReal.ofReal_pow h0]
  have hL' : ∫⁻ ω, ENNReal.ofReal (E M.T ω ^ 2) ∂μ = ∫⁻ ω, ‖E M.T ω‖ₑ ^ 2 ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [h0] with ω h0
    rw [Real.enorm_eq_ofReal h0, ENNReal.ofReal_pow h0]
  have hfin : ∫⁻ ω, (M.Qm E).rnDeriv μ ω ^ 2 ∂μ < ⊤ := by rw [hL, hL']; exact h2
  refine (iInf₂_le (M.Qm E) ⟨hQp, hQP, hfin⟩).trans_eq ?_
  congr 3
  rw [hL, integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => sq_nonneg _)
    (hEi.aestronglyMeasurable.pow 2)]
