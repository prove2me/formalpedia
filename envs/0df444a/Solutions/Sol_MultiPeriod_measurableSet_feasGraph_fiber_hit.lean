-- Prove2me | solution 1 for MultiPeriod.measurableSet_feasGraph_fiber_hit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:31:50.919192+00:00
-- url     : https://prove2.me/submissions/417892b7-c240-4d1b-aa04-b1f067e7da8a

import Definitions.Def_BicausalOT_MeasurableStrategy
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Definitions.Def_BicausalOT_LscBellman
import Theorems.Thm_MultiPeriod_continuous_projX
import Theorems.Thm_MultiPeriod_continuous_projY
import Theorems.Thm_isClosed_couplings_hit


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
theorem _root_.solution
    (hκμ_cont : ∀ t, Continuous (κμP t))
    (hκν_cont : ∀ t, Continuous (κνP t)) (t : ℕ)
    {C : Set (WeakP (X (t + 1) × Y (t + 1)))} (hC : IsClosed C) :
    MeasurableSet {h : PairHist X Y t |
      ({γ | (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t} ∩ C).Nonempty} := by
  have hm : Continuous (fun h : PairHist X Y t =>
      (κμP t (projX t h), κνP t (projY t h))) :=
    ((hκμ_cont t).comp (continuous_projX t)).prodMk
      ((hκν_cont t).comp (continuous_projY t))
  have hhit : IsClosed {p : ProbabilityMeasure (X (t + 1))
      × ProbabilityMeasure (Y (t + 1)) |
      ∃ γ : ProbabilityMeasure ((X (t + 1)) × (Y (t + 1))), γ ∈ C ∧
        (γ : Measure ((X (t + 1)) × (Y (t + 1)))).map Prod.fst
          = (p.1 : Measure (X (t + 1))) ∧
        (γ : Measure ((X (t + 1)) × (Y (t + 1)))).map Prod.snd
          = (p.2 : Measure (Y (t + 1)))} :=
    isClosed_couplings_hit hC
  have hset : {h : PairHist X Y t |
      ({γ | (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t} ∩ C).Nonempty}
      = (fun h : PairHist X Y t =>
          (κμP t (projX t h), κνP t (projY t h))) ⁻¹'
        {p : ProbabilityMeasure (X (t + 1))
            × ProbabilityMeasure (Y (t + 1)) |
          ∃ γ : ProbabilityMeasure ((X (t + 1)) × (Y (t + 1))), γ ∈ C ∧
            (γ : Measure ((X (t + 1)) × (Y (t + 1)))).map Prod.fst
              = (p.1 : Measure (X (t + 1))) ∧
            (γ : Measure ((X (t + 1)) × (Y (t + 1)))).map Prod.snd
              = (p.2 : Measure (Y (t + 1)))} := by
    ext h
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · rintro ⟨γ, hfib, hγC⟩
      exact ⟨γ, hγC, hfib.1, hfib.2⟩
    · rintro ⟨γ, hγC, hfst, hsnd⟩
      exact ⟨γ, ⟨hfst, hsnd⟩, hγC⟩
  rw [hset]
  exact (hhit.preimage hm).measurableSet
end MultiPeriod
