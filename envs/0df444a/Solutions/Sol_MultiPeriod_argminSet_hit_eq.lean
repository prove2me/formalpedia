-- Prove2me | solution 1 for MultiPeriod.argminSet_hit_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:31:48.930795+00:00
-- url     : https://prove2.me/submissions/0a1a375f-6770-4d57-bfbf-9412281b8b13

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
    (hF : LowerSemicontinuous F)
    {C : Set (WeakP (X (t + 1) × Y (t + 1)))} (hC : IsClosed C) :
    {h | (argminSet κμP κνP t F h ∩ C).Nonempty}
      = {h | ({γ | (h, γ) ∈ FeasGraph
            (fun t x => (κμP t x : Measure (X (t + 1))))
            (fun t y => (κνP t y : Measure (Y (t + 1)))) t} ∩ C).Nonempty}
        ∩ {h | stageMin κμP κνP t F C h ≤ stageMin κμP κνP t F univ h} := by
  ext h
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨γ, ⟨hfib, hopt⟩, hγC⟩
    exact ⟨⟨γ, hfib, hγC⟩, le_trans (iInf₂_le γ ⟨hfib, hγC⟩) hopt⟩
  · rintro ⟨⟨γ₀, hγ₀fib, hγ₀C⟩, hle⟩
    have hcomp : IsCompact ({γ : WeakP (X (t + 1) × Y (t + 1)) |
        (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
          (fun t y => (κνP t y : Measure (Y (t + 1)))) t} ∩ C) :=
      (isCompact_feasGraph_fiber κμP κνP t h).inter_right hC
    have hne' : ({γ : WeakP (X (t + 1) × Y (t + 1)) |
        (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
          (fun t y => (κνP t y : Measure (Y (t + 1)))) t} ∩ C).Nonempty :=
      ⟨γ₀, hγ₀fib, hγ₀C⟩
    obtain ⟨γ, hγmem, hγmin⟩ := LowerSemicontinuousOn.exists_isMinOn
      hne' hcomp
      ((hF.comp (Continuous.prodMk continuous_const continuous_id)
        ).lowerSemicontinuousOn _)
    refine ⟨γ, ⟨hγmem.1, le_trans ?_ hle⟩, hγmem.2⟩
    exact le_iInf₂ fun γ' hγ' => isMinOn_iff.mp hγmin γ' ⟨hγ'.1, hγ'.2⟩
end MultiPeriod
