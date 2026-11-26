-- Prove2me | solution 1 for MultiPeriod.stageF_lowerSemianalytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:17:12.983383+00:00
-- url     : https://prove2.me/submissions/02ae6c71-d981-4e6b-b4b9-4bccd78e07d1

import Definitions.Def_BicausalOT_SemianalyticValue
import Definitions.Def_BicausalOT_DescriptiveSetTheory_EpsOptimalSelection
import Definitions.Def_BicausalOT_MeasurableStrategy
import Theorems.Thm_MultiPeriod_VGo_isLowerSemianalytic
import Theorems.Thm_MultiPeriod_lintegral_weakP_lowerSemianalytic


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
theorem _root_.solution
    (hκμ_meas : ∀ t, Measurable (κμ t))
    (hκν_meas : ∀ t, Measurable (κν t))
    (hκμ_prob : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hκν_prob : ∀ t y, IsProbabilityMeasure (κν t y))
    (hc : ∀ t, IsLowerSemianalytic (c t)) (k t : ℕ) :
    IsLowerSemianalytic
      (fun p : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) =>
        ∫⁻ z, VGo c κμ κν k (t + 1) (p.1, z) ∂p.2.toMeasure) :=
  lintegral_weakP_lowerSemianalytic t
    (VGo_isLowerSemianalytic κμ κν c hκμ_meas hκν_meas hκμ_prob
      hκν_prob hc k (t + 1))
end MultiPeriod
