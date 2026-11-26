-- Prove2me | solution 1 for MultiPeriod.measurableSet_argminSet_hit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:33:07.236901+00:00
-- url     : https://prove2.me/submissions/2794398a-0a87-4ac2-a394-8a15894dd7af

import Definitions.Def_BicausalOT_MeasurableStrategy
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Definitions.Def_BicausalOT_LscBellman
import Theorems.Thm_MultiPeriod_lowerSemicontinuous_stageMin
import Theorems.Thm_MultiPeriod_argminSet_hit_eq
import Theorems.Thm_MultiPeriod_measurableSet_feasGraph_fiber_hit
import Theorems.Thm_IsOpen_exists_iUnion_isClosed_of_pseudoMetrizable


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
    {F : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) → ℝ≥0∞}
    (hF : LowerSemicontinuous F)
    {U : Set (WeakP (X (t + 1) × Y (t + 1)))} (hU : IsOpen U) :
    MeasurableSet {h | (argminSet κμP κνP t F h ∩ U).Nonempty} := by
  obtain ⟨C, hCclosed, hUeq⟩ := hU.exists_iUnion_isClosed_of_pseudoMetrizable
  have hsplit : {h | (argminSet κμP κνP t F h ∩ U).Nonempty}
      = ⋃ n, {h | (argminSet κμP κνP t F h ∩ C n).Nonempty} := by
    rw [hUeq]
    ext h
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨γ, hγa, hγU⟩
      obtain ⟨n, hγn⟩ := Set.mem_iUnion.mp hγU
      exact ⟨n, γ, hγa, hγn⟩
    · rintro ⟨n, γ, hγa, hγn⟩
      exact ⟨γ, hγa, Set.mem_iUnion.mpr ⟨n, hγn⟩⟩
  rw [hsplit]
  refine MeasurableSet.iUnion fun n => ?_
  rw [argminSet_hit_eq κμP κνP t hF (hCclosed n)]
  exact (measurableSet_feasGraph_fiber_hit κμP κνP hκμ_cont hκν_cont t
      (hCclosed n)).inter
    (measurableSet_le
      (lowerSemicontinuous_stageMin κμP κνP hκμ_cont hκν_cont t hF
        (hCclosed n)).measurable
      (lowerSemicontinuous_stageMin κμP κνP hκμ_cont hκν_cont t hF
        isClosed_univ).measurable)
end MultiPeriod
