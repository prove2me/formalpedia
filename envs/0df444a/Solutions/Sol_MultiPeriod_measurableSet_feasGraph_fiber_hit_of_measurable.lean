-- Prove2me | solution 1 for MultiPeriod.measurableSet_feasGraph_fiber_hit_of_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:32:56.640626+00:00
-- url     : https://prove2.me/submissions/76b4cbc7-0e59-4960-979a-3539b96b47c8

import Definitions.Def_BicausalOT_LscBellman
import Definitions.Def_BicausalOT_MeasurableFeasibleStrategy
import Theorems.Thm_IsOpen_exists_iUnion_isClosed_of_pseudoMetrizable
import Theorems.Thm_MultiPeriod_measurable_projX
import Theorems.Thm_MultiPeriod_measurable_projY
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
namespace MultiPeriod
theorem _root_.solution
    (hκμ_measW : ∀ t, @Measurable (XHist X t) (WeakP (X (t + 1)))
      _ _ (κμP t))
    (hκν_measW : ∀ t, @Measurable (YHist Y t) (WeakP (Y (t + 1)))
      _ _ (κνP t)) (t : ℕ)
    {U : Set (WeakP (X (t + 1) × Y (t + 1)))} (hU : IsOpen U) :
    MeasurableSet {h : PairHist X Y t |
      ({γ | (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t} ∩ U).Nonempty} := by
  obtain ⟨C, hCclosed, hUeq⟩ := hU.exists_iUnion_isClosed_of_pseudoMetrizable
  have hsplit : {h : PairHist X Y t |
      ({γ | (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t} ∩ U).Nonempty}
      = ⋃ n, {h : PairHist X Y t |
        ({γ | (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
          (fun t y => (κνP t y : Measure (Y (t + 1)))) t} ∩ C n).Nonempty} := by
    rw [hUeq]
    ext h
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨γ, hγfib, hγU⟩
      obtain ⟨n, hγn⟩ := Set.mem_iUnion.mp hγU
      exact ⟨n, γ, hγfib, hγn⟩
    · rintro ⟨n, γ, hγfib, hγn⟩
      exact ⟨γ, hγfib, Set.mem_iUnion.mpr ⟨n, hγn⟩⟩
  rw [hsplit]
  refine MeasurableSet.iUnion fun n => ?_
  -- the marginal-pair map is measurable into the WeakP product
  have hm : @Measurable (PairHist X Y t)
      (WeakP (X (t + 1)) × WeakP (Y (t + 1))) _ _
      (fun h => (κμP t (projX t h), κνP t (projY t h))) :=
    ((hκμ_measW t).comp (measurable_projX t)).prodMk
      ((hκν_measW t).comp (measurable_projY t))
  -- the closed couplings hit-set is Borel in the WeakP product
  have hhit : IsClosed {p : ProbabilityMeasure (X (t + 1))
      × ProbabilityMeasure (Y (t + 1)) |
      ∃ γ : ProbabilityMeasure ((X (t + 1)) × (Y (t + 1))), γ ∈ C n ∧
        (γ : Measure ((X (t + 1)) × (Y (t + 1)))).map Prod.fst
          = (p.1 : Measure (X (t + 1))) ∧
        (γ : Measure ((X (t + 1)) × (Y (t + 1)))).map Prod.snd
          = (p.2 : Measure (Y (t + 1)))} :=
    isClosed_couplings_hit (hCclosed n)
  have hhitW : IsClosed {p : WeakP (X (t + 1)) × WeakP (Y (t + 1)) |
      ∃ γ : ProbabilityMeasure ((X (t + 1)) × (Y (t + 1))), γ ∈ C n ∧
        (γ : Measure ((X (t + 1)) × (Y (t + 1)))).map Prod.fst
          = p.1.toMeasure ∧
        (γ : Measure ((X (t + 1)) × (Y (t + 1)))).map Prod.snd
          = p.2.toMeasure} := hhit
  have hhitmeas := hhitW.measurableSet
  have hset : {h : PairHist X Y t |
      ({γ | (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t} ∩ C n).Nonempty}
      = (fun h : PairHist X Y t =>
          ((κμP t (projX t h), κνP t (projY t h))
            : WeakP (X (t + 1)) × WeakP (Y (t + 1)))) ⁻¹'
        {p : WeakP (X (t + 1)) × WeakP (Y (t + 1)) |
          ∃ γ : ProbabilityMeasure ((X (t + 1)) × (Y (t + 1))), γ ∈ C n ∧
            (γ : Measure ((X (t + 1)) × (Y (t + 1)))).map Prod.fst
              = p.1.toMeasure ∧
            (γ : Measure ((X (t + 1)) × (Y (t + 1)))).map Prod.snd
              = p.2.toMeasure} := by
    ext h
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · rintro ⟨γ, hγfib, hγC⟩
      exact ⟨γ, hγC, hγfib.1, hγfib.2⟩
    · rintro ⟨γ, hγC, hfst, hsnd⟩
      exact ⟨γ, ⟨hfst, hsnd⟩, hγC⟩
  rw [hset]
  exact hm hhitmeas
end MultiPeriod
