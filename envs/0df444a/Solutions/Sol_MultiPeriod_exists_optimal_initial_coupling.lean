-- Prove2me | solution 1 for MultiPeriod.exists_optimal_initial_coupling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:35:59.043679+00:00
-- url     : https://prove2.me/submissions/db33bcd9-8e58-47a6-8889-20ff6191682d

import Definitions.Def_BicausalOT_MeasurableStrategy
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Definitions.Def_BicausalOT_LscBellman
import Theorems.Thm_P2M_MultiPeriod_iInf_couplingSet__eq_iInf_weakP_9d2e42b6cc02
import Theorems.Thm_P2M_MultiPeriod_isCompact_couplingSet__weakP_4b4f4e3463e6
import Theorems.Thm_P2M_MultiPeriod_couplingSet__weakP_nonempty_46c7c592b32c
import Theorems.Thm_MultiPeriod_lowerSemicontinuous_lintegral_VGo

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
    ∃ γ₀ : Measure (X 0 × Y 0), γ₀ ∈ CouplingSet₀ μ₀ ν₀ ∧
      IsProbabilityMeasure γ₀ ∧
      ∫⁻ h₀, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
          (fun t y => (κνP t y : Measure (Y (t + 1)))) T 0 h₀ ∂γ₀
        = ⨅ (γ₀' : Measure (X 0 × Y 0)) (_ : γ₀' ∈ CouplingSet₀ μ₀ ν₀),
            ∫⁻ h₀, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
              (fun t y => (κνP t y : Measure (Y (t + 1)))) T 0 h₀ ∂γ₀' := by
  obtain ⟨γstar, hmem, hmin⟩ :=
    LowerSemicontinuousOn.exists_isMinOn
      (couplingSet₀_weakP_nonempty (X := X) (Y := Y) μ₀ ν₀)
      (isCompact_couplingSet₀_weakP (X := X) (Y := Y) μ₀ ν₀)
      ((lowerSemicontinuous_lintegral_VGo κμP κνP c T hκμ_cont hκν_cont
        hc).lowerSemicontinuousOn _)
  refine ⟨γstar.toMeasure, hmem, inferInstance, ?_⟩
  have hbridge :
      (⨅ (γ₀' : Measure (X 0 × Y 0)) (_ : γ₀' ∈ CouplingSet₀ μ₀ ν₀),
          ∫⁻ h₀, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
            (fun t y => (κνP t y : Measure (Y (t + 1)))) T 0 h₀ ∂γ₀')
        = ⨅ (γ : WeakP (X 0 × Y 0))
            (_ : γ.toMeasure ∈ CouplingSet₀ μ₀ ν₀),
            ∫⁻ h₀, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
              (fun t y => (κνP t y : Measure (Y (t + 1)))) T 0 h₀
              ∂γ.toMeasure :=
    iInf_couplingSet₀_eq_iInf_weakP (X := X) (Y := Y) μ₀ ν₀ _
  rw [hbridge]
  exact le_antisymm (le_iInf₂ fun γ hγ => isMinOn_iff.mp hmin γ hγ)
    (iInf₂_le γstar hmem)
end MultiPeriod
