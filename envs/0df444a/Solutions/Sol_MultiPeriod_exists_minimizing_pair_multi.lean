-- Prove2me | solution 1 for MultiPeriod.exists_minimizing_pair_multi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:39:42.68779+00:00
-- url     : https://prove2.me/submissions/0efd3114-8e91-4224-a337-e8ad5af973e8

import Definitions.Def_BicausalOT_MeasurableStrategy
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Definitions.Def_BicausalOT_LscBellman
import Theorems.Thm_MultiPeriod_bellman_value_attained_multi

set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
open MultiPeriod
variable {X Y : ℕ → Type*}
  [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
  [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
variable (κμP : (t : ℕ) → XHist X t → ProbabilityMeasure (X (t + 1)))
variable (κνP : (t : ℕ) → YHist Y t → ProbabilityMeasure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)
namespace MultiPeriod
theorem _root_.solution (T : ℕ)
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (ν₀ : Measure (Y 0)) [IsProbabilityMeasure ν₀]
    (hκμ_cont : ∀ t, Continuous (κμP t))
    (hκν_cont : ∀ t, Continuous (κνP t))
    (hc : ∀ t, LowerSemicontinuous (c t)) :
    ∃ (γ₀ : Measure (X 0 × Y 0)) (γopt : Strat X Y),
      γ₀ ∈ CouplingSet₀ μ₀ ν₀ ∧
      (∀ t h, γopt t h ∈ Feas (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t h) ∧
      (∀ t, ∃ φ : PairHist X Y t → WeakP (X (t + 1) × Y (t + 1)),
        Measurable φ ∧ ∀ h, γopt t h = (φ h).toMeasure) ∧
      ∀ (γ₀' : Measure (X 0 × Y 0)) (γ : Strat X Y),
        γ₀' ∈ CouplingSet₀ μ₀ ν₀ →
        (∀ t h, γ t h ∈ Feas (fun t x => (κμP t x : Measure (X (t + 1))))
          (fun t y => (κνP t y : Measure (Y (t + 1)))) t h) →
        ∫⁻ h₀, costGo c γopt T 0 h₀ ∂γ₀
          ≤ ∫⁻ h₀, costGo c γ T 0 h₀ ∂γ₀' := by
  obtain ⟨γ₀, γopt, hγ₀mem, -, hfeas, hφ, hval⟩ :=
    bellman_value_attained_multi κμP κνP c T μ₀ ν₀ hκμ_cont hκν_cont hc
  refine ⟨γ₀, γopt, hγ₀mem, hfeas, hφ, fun γ₀' γ hmem' hfeas' => ?_⟩
  rw [hval]
  exact iInf_le_of_le γ₀' (iInf_le_of_le γ
    (iInf_le_of_le hmem' (iInf_le _ hfeas')))
end MultiPeriod
