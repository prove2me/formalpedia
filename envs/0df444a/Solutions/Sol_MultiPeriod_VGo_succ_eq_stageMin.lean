-- Prove2me | solution 1 for MultiPeriod.VGo_succ_eq_stageMin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:31:40.547471+00:00
-- url     : https://prove2.me/submissions/b9ce76ec-f6b2-4458-8734-78cde0b2e806

import Definitions.Def_BicausalOT_MeasurableStrategy
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Definitions.Def_BicausalOT_LscBellman
import Theorems.Thm_MultiPeriod_VGo_succ_eq_weakP


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
omit [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, BorelSpace (X n)] [∀ n, TopologicalSpace (Y n)]
  [∀ n, PolishSpace (Y n)] [∀ n, BorelSpace (Y n)]
namespace MultiPeriod
theorem _root_.solution (k t : ℕ) (h : PairHist X Y t) :
    VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) (k + 1) t h
      = c t h + stageMin κμP κνP t
          (fun p => ∫⁻ z, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
            (fun t y => (κνP t y : Measure (Y (t + 1)))) k (t + 1) (p.1, z)
            ∂p.2.toMeasure) univ h := by
  rw [VGo_succ_eq_weakP _ _ c (fun _ _ => inferInstance) k t h]
  congr 1
  simp only [stageMin, Set.mem_univ, and_true]
end MultiPeriod
