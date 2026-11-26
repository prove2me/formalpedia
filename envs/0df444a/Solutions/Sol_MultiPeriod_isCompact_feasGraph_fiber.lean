-- Prove2me | solution 1 for MultiPeriod.isCompact_feasGraph_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:30:20.32766+00:00
-- url     : https://prove2.me/submissions/39295a69-fe7a-48fa-856c-4cadd2cbd300

import Definitions.Def_BicausalOT_MeasurableStrategy
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Definitions.Def_BicausalOT_LscBellman
import Theorems.Thm_isCompact_probabilityMeasure_marginals


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
theorem _root_.solution (t : ℕ) (h : PairHist X Y t) :
    IsCompact {γ : WeakP (X (t + 1) × Y (t + 1)) |
      (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t} :=
  isCompact_probabilityMeasure_marginals
    (κμP t (projX t h) : Measure (X (t + 1)))
    (κνP t (projY t h) : Measure (Y (t + 1)))
end MultiPeriod
