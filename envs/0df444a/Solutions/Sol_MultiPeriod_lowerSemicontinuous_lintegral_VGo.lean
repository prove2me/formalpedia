-- Prove2me | solution 1 for MultiPeriod.lowerSemicontinuous_lintegral_VGo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:34:43.429808+00:00
-- url     : https://prove2.me/submissions/092ce15d-53be-4755-b20f-22e879299ee4

import Definitions.Def_BicausalOT_MeasurableStrategy
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Definitions.Def_BicausalOT_LscBellman
import Theorems.Thm_MultiPeriod_lowerSemicontinuous_VGo
import Theorems.Thm_lowerSemicontinuous_lintegral_probabilityMeasure


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
    LowerSemicontinuous (fun γ : WeakP (X 0 × Y 0) =>
      ∫⁻ h₀, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) T 0 h₀
        ∂γ.toMeasure) := by
  have hlsc : LowerSemicontinuous
      (fun h₀ : X 0 × Y 0 =>
        VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
          (fun t y => (κνP t y : Measure (Y (t + 1)))) T 0 h₀) :=
    lowerSemicontinuous_VGo κμP κνP c hκμ_cont hκν_cont hc T 0
  exact lowerSemicontinuous_lintegral_probabilityMeasure hlsc
end MultiPeriod
