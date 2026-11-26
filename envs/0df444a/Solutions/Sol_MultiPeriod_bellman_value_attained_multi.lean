-- Prove2me | solution 1 for MultiPeriod.bellman_value_attained_multi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:37:56.30149+00:00
-- url     : https://prove2.me/submissions/1ce63644-516f-48a3-8a17-1b4ae7f2fc93

import Definitions.Def_BicausalOT_MeasurableStrategy
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Definitions.Def_BicausalOT_LscBellman
import Theorems.Thm_MultiPeriod_bellman_value_attained_measurable
import Theorems.Thm_MultiPeriod_exists_optimal_initial_coupling
import Theorems.Thm_P2M_MultiPeriod_bellman_value_eq_multi__0ac808a7f4a2


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
      IsProbabilityMeasure γ₀ ∧
      (∀ t h, γopt t h ∈ Feas (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t h) ∧
      (∀ t, ∃ φ : PairHist X Y t → WeakP (X (t + 1) × Y (t + 1)),
        Measurable φ ∧ ∀ h, γopt t h = (φ h).toMeasure) ∧
      ∫⁻ h₀, costGo c γopt T 0 h₀ ∂γ₀
        = ⨅ (γ₀' : Measure (X 0 × Y 0)) (γ : Strat X Y)
            (_ : γ₀' ∈ CouplingSet₀ μ₀ ν₀)
            (_ : ∀ t h, γ t h ∈ Feas
              (fun t x => (κμP t x : Measure (X (t + 1))))
              (fun t y => (κνP t y : Measure (Y (t + 1)))) t h),
            ∫⁻ h₀, costGo c γ T 0 h₀ ∂γ₀' := by
  obtain ⟨γopt, hfeas, hφ, hcost⟩ :=
    bellman_value_attained_measurable κμP κνP c T hκμ_cont hκν_cont hc
  obtain ⟨γ₀, hγ₀mem, hγ₀prob, hγ₀min⟩ :=
    exists_optimal_initial_coupling κμP κνP c T μ₀ ν₀ hκμ_cont hκν_cont hc
  refine ⟨γ₀, γopt, hγ₀mem, hγ₀prob, hfeas, hφ, ?_⟩
  have hmulti :=
    bellman_value_eq_multi' (fun t x => (κμP t x : Measure (X (t + 1))))
      (fun t y => (κνP t y : Measure (Y (t + 1)))) c T μ₀ ν₀
      (fun _ _ => inferInstance) (fun _ _ => inferInstance)
  calc ∫⁻ h₀, costGo c γopt T 0 h₀ ∂γ₀
      = ∫⁻ h₀, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
          (fun t y => (κνP t y : Measure (Y (t + 1)))) T 0 h₀ ∂γ₀ :=
        lintegral_congr fun h₀ => hcost h₀
    _ = ⨅ (γ₀' : Measure (X 0 × Y 0)) (_ : γ₀' ∈ CouplingSet₀ μ₀ ν₀),
          ∫⁻ h₀, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
            (fun t y => (κνP t y : Measure (Y (t + 1)))) T 0 h₀ ∂γ₀' :=
        hγ₀min
    _ = ⨅ (γ₀' : Measure (X 0 × Y 0)) (γ : Strat X Y)
          (_ : γ₀' ∈ CouplingSet₀ μ₀ ν₀)
          (_ : ∀ t h, γ t h ∈ Feas
            (fun t x => (κμP t x : Measure (X (t + 1))))
            (fun t y => (κνP t y : Measure (Y (t + 1)))) t h),
          ∫⁻ h₀, costGo c γ T 0 h₀ ∂γ₀' := hmulti.symm
end MultiPeriod
