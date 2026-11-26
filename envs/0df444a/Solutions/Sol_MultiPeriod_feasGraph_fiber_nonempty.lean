-- Prove2me | solution 1 for MultiPeriod.feasGraph_fiber_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:15:12.771436+00:00
-- url     : https://prove2.me/submissions/2bf0ba23-e6b1-406a-9ce8-7e124be00c91

import Definitions.Def_BicausalOT_SemianalyticValue
import Definitions.Def_BicausalOT_DescriptiveSetTheory_EpsOptimalSelection
import Definitions.Def_BicausalOT_MeasurableStrategy
import Theorems.Thm_MultiPeriod_Feas_measure_univ
import Theorems.Thm_P2M_CouplingSet__measure_univ_db95189062ba


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
omit [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, BorelSpace (X n)] [∀ n, TopologicalSpace (Y n)]
  [∀ n, PolishSpace (Y n)] [∀ n, BorelSpace (Y n)]
namespace MultiPeriod
theorem _root_.solution
    (hκμ_prob : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hne : ∀ t (h : PairHist X Y t), (Feas κμ κν t h).Nonempty)
    (t : ℕ) (h : PairHist X Y t) :
    ∃ γ : WeakP (X (t + 1) × Y (t + 1)), (h, γ) ∈ FeasGraph κμ κν t := by
  obtain ⟨γm, hγm⟩ := hne t h
  haveI hpm : IsProbabilityMeasure γm :=
    ⟨Feas.measure_univ κμ κν hκμ_prob hγm⟩
  exact ⟨show WeakP (X (t + 1) × Y (t + 1)) from
    (⟨γm, hpm⟩ : ProbabilityMeasure (X (t + 1) × Y (t + 1))), hγm⟩
end MultiPeriod
