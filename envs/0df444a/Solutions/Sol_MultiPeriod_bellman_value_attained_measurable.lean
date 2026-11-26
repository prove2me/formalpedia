-- Prove2me | solution 1 for MultiPeriod.bellman_value_attained_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:36:10.014858+00:00
-- url     : https://prove2.me/submissions/53123a78-7da1-4b37-8ba7-69bd9c368711

import Definitions.Def_BicausalOT_MeasurableStrategy
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Definitions.Def_BicausalOT_LscBellman
import Theorems.Thm_MultiPeriod_exists_optimal_measurable_strategy
import Theorems.Thm_MultiPeriod_costGo_eq_VGo_of_optimal

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
    (hκμ_cont : ∀ t, Continuous (κμP t))
    (hκν_cont : ∀ t, Continuous (κνP t))
    (hc : ∀ t, LowerSemicontinuous (c t)) :
    ∃ γopt : Strat X Y,
      (∀ t h, γopt t h ∈ Feas (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t h) ∧
      (∀ t, ∃ φ : PairHist X Y t → WeakP (X (t + 1) × Y (t + 1)),
        Measurable φ ∧ ∀ h, γopt t h = (φ h).toMeasure) ∧
      ∀ h₀ : PairHist X Y 0,
        costGo c γopt T 0 h₀
          = VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
              (fun t y => (κνP t y : Measure (Y (t + 1)))) T 0 h₀ := by
  obtain ⟨γopt, hmem, hopt, hφ⟩ :=
    exists_optimal_measurable_strategy κμP κνP c T hκμ_cont hκν_cont hc
  exact ⟨γopt, hmem, hφ,
    fun h₀ => costGo_eq_VGo_of_optimal c T (fun _ _ => inferInstance)
      γopt hmem hopt T 0 (by omega) h₀⟩
end MultiPeriod
