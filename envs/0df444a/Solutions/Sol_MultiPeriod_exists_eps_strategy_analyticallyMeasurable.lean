-- Prove2me | solution 1 for MultiPeriod.exists_eps_strategy_analyticallyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:18:20.099946+00:00
-- url     : https://prove2.me/submissions/13e22a2f-5629-44a3-a480-8f4ea6da15ee

import Definitions.Def_BicausalOT_SemianalyticValue
import Definitions.Def_BicausalOT_DescriptiveSetTheory_EpsOptimalSelection
import Definitions.Def_BicausalOT_MeasurableStrategy
import Theorems.Thm_MultiPeriod_feasGraph_fiber_nonempty
import Theorems.Thm_MultiPeriod_stageF_lowerSemianalytic
import Theorems.Thm_IsOpen_analyticSet
import Theorems.Thm_MultiPeriod_iInf_feas_eq_iInf_feasGraph
import Theorems.Thm_MultiPeriod_measurableSet_feasGraph
import Theorems.Thm_exists_eps_optimal_selector


set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
open MultiPeriod
variable {X Y : ℕ → Type*}
  [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
  [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
variable (κμ : (t : ℕ) → XHist X t → Measure (X (t + 1)))
variable (κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)
namespace MultiPeriod
theorem _root_.solution (T : ℕ)
    (hκμ_meas : ∀ t, Measurable (κμ t))
    (hκν_meas : ∀ t, Measurable (κν t))
    (hκμ_prob : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hκν_prob : ∀ t y, IsProbabilityMeasure (κν t y))
    (hc : ∀ t, IsLowerSemianalytic (c t))
    (hne : ∀ t (h : PairHist X Y t), (Feas κμ κν t h).Nonempty)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ γε : Strat X Y,
      (∀ t h, γε t h ∈ Feas κμ κν t h) ∧
      (∀ t (h : PairHist X Y t),
        ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂(γε t h)
          ≤ (⨅ (γm : Measure (X (t + 1) × Y (t + 1)))
              (_ : γm ∈ Feas κμ κν t h),
              ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂γm) + ε) ∧
      (∀ t, ∃ φ : PairHist X Y t → WeakP (X (t + 1) × Y (t + 1)),
        AnalyticallyMeasurable φ ∧ ∀ h, γε t h = (φ h).toMeasure) := by
  have key : ∀ t : ℕ,
      ∃ φ : PairHist X Y t → WeakP (X (t + 1) × Y (t + 1)),
      AnalyticallyMeasurable φ ∧
      (∀ h, (h, φ h) ∈ FeasGraph κμ κν t) ∧
      ∀ h, (∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂(φ h).toMeasure)
        ≤ (⨅ (γ : WeakP (X (t + 1) × Y (t + 1)))
            (_ : (h, γ) ∈ FeasGraph κμ κν t),
            ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂γ.toMeasure)
          + ε :=
    fun t => exists_eps_optimal_selector
      ((measurableSet_feasGraph κμ κν hκμ_meas hκν_meas hκμ_prob
        hκν_prob t).analyticSet)
      (stageF_lowerSemianalytic κμ κν c hκμ_meas hκν_meas hκμ_prob
        hκν_prob hc (T - t - 1) t)
      (feasGraph_fiber_nonempty κμ κν hκμ_prob hne t) hε
  choose φ hφmeas hφmem hφopt using key
  refine ⟨fun t h => (φ t h).toMeasure,
    fun t h => hφmem t h,
    fun t h => ?_,
    fun t => ⟨φ t, hφmeas t, fun h => rfl⟩⟩
  rw [iInf_feas_eq_iInf_feasGraph κμ κν hκμ_prob t h]
  exact hφopt t h
end MultiPeriod
