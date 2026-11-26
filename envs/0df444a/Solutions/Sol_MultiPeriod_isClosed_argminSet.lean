-- Prove2me | solution 1 for MultiPeriod.isClosed_argminSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:31:46.566803+00:00
-- url     : https://prove2.me/submissions/2b1281f9-cda9-498b-9002-ccbd3c5e896d

import Definitions.Def_BicausalOT_MeasurableStrategy
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Definitions.Def_BicausalOT_LscBellman
import Theorems.Thm_MultiPeriod_isCompact_feasGraph_fiber

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
theorem _root_.solution (t : ℕ)
    {F : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) → ℝ≥0∞}
    (hF : LowerSemicontinuous F) (h : PairHist X Y t) :
    IsClosed (argminSet κμP κνP t F h) := by
  have h1 : IsClosed {γ : WeakP (X (t + 1) × Y (t + 1)) |
      (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t} :=
    (isCompact_feasGraph_fiber κμP κνP t h).isClosed
  have h2 : IsClosed {γ : WeakP (X (t + 1) × Y (t + 1)) |
      F (h, γ) ≤ stageMin κμP κνP t F univ h} :=
    (lowerSemicontinuous_iff_isClosed_preimage.mp
      (hF.comp (Continuous.prodMk continuous_const continuous_id))) _
  exact h1.inter h2
end MultiPeriod
