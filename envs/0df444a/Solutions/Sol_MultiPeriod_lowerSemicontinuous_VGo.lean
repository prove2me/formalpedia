-- Prove2me | solution 1 for MultiPeriod.lowerSemicontinuous_VGo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:32:53.469576+00:00
-- url     : https://prove2.me/submissions/46ca9ab0-0b84-41ff-9501-f547d39b0d46

import Definitions.Def_BicausalOT_MeasurableStrategy
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Definitions.Def_BicausalOT_LscBellman
import Theorems.Thm_MultiPeriod_VGo_succ_eq_stageMin
import Theorems.Thm_MultiPeriod_lowerSemicontinuous_stageMin
import Theorems.Thm_IsLowerSemianalytic_add
import Theorems.Thm_lowerSemicontinuous_lintegral_prodMk


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
    (hκν_cont : ∀ t, Continuous (κνP t))
    (hc : ∀ t, LowerSemicontinuous (c t)) :
    ∀ k t : ℕ, LowerSemicontinuous
      (VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) k t) := by
  intro k
  induction k with
  | zero => exact fun t => hc t
  | succ k ih =>
    intro t
    have heq : VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) (k + 1) t
        = fun h => c t h + stageMin κμP κνP t
            (fun p => ∫⁻ z, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
              (fun t y => (κνP t y : Measure (Y (t + 1)))) k (t + 1) (p.1, z)
              ∂p.2.toMeasure) univ h :=
      funext fun h => VGo_succ_eq_stageMin κμP κνP c k t h
    rw [heq]
    have hFk : LowerSemicontinuous
        (fun p : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) =>
          ∫⁻ z, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
            (fun t y => (κνP t y : Measure (Y (t + 1)))) k (t + 1) (p.1, z)
            ∂p.2.toMeasure) := by
      have hf : LowerSemicontinuous
          (fun q : PairHist X Y t × (X (t + 1) × Y (t + 1)) =>
            VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
              (fun t y => (κνP t y : Measure (Y (t + 1)))) k (t + 1)
              (q.1, q.2)) := ih (t + 1)
      exact lowerSemicontinuous_lintegral_prodMk hf
    exact (hc t).add
      (lowerSemicontinuous_stageMin κμP κνP hκμ_cont hκν_cont t hFk
        isClosed_univ)
end MultiPeriod
