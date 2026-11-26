-- Prove2me | solution 1 for MultiPeriod.exists_optimal_measurable_strategy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:34:42.946983+00:00
-- url     : https://prove2.me/submissions/16ca6b4f-fb2f-4ee3-82f1-7459af5a09c0

import Definitions.Def_BicausalOT_MeasurableStrategy
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Definitions.Def_BicausalOT_LscBellman
import Theorems.Thm_WeakP_exists_measurable_selection
import Theorems.Thm_MultiPeriod_lowerSemicontinuous_VGo
import Theorems.Thm_MultiPeriod_argminSet_nonempty
import Theorems.Thm_MultiPeriod_isClosed_argminSet
import Theorems.Thm_MultiPeriod_measurableSet_argminSet_hit
import Theorems.Thm_MultiPeriod_iInf_feas_eq_iInf_feasGraph
import Theorems.Thm_exists_measurable_selection
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
theorem _root_.solution (T : ℕ)
    (hκμ_cont : ∀ t, Continuous (κμP t))
    (hκν_cont : ∀ t, Continuous (κνP t))
    (hc : ∀ t, LowerSemicontinuous (c t)) :
    ∃ γopt : Strat X Y,
      (∀ t h, γopt t h ∈ Feas (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t h) ∧
      (∀ t (h : PairHist X Y t),
        ∫⁻ z, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
            (fun t y => (κνP t y : Measure (Y (t + 1)))) (T - t - 1) (t + 1)
            (h, z) ∂(γopt t h)
          ≤ ⨅ (γm : Measure (X (t + 1) × Y (t + 1)))
              (_ : γm ∈ Feas (fun t x => (κμP t x : Measure (X (t + 1))))
                (fun t y => (κνP t y : Measure (Y (t + 1)))) t h),
              ∫⁻ z, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
                (fun t y => (κνP t y : Measure (Y (t + 1)))) (T - t - 1)
                (t + 1) (h, z) ∂γm) ∧
      (∀ t, ∃ φ : PairHist X Y t → WeakP (X (t + 1) × Y (t + 1)),
        Measurable φ ∧ ∀ h, γopt t h = (φ h).toMeasure) := by
  have key : ∀ t : ℕ, ∃ φ : PairHist X Y t → WeakP (X (t + 1) × Y (t + 1)),
      Measurable φ ∧ ∀ h, φ h ∈ argminSet κμP κνP t
        (fun p => ∫⁻ z, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
          (fun t y => (κνP t y : Measure (Y (t + 1)))) (T - t - 1) (t + 1)
          (p.1, z) ∂p.2.toMeasure) h := by
    intro t
    have hF : LowerSemicontinuous
        (fun p : PairHist X Y t × WeakP (X (t + 1) × Y (t + 1)) =>
          ∫⁻ z, VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
            (fun t y => (κνP t y : Measure (Y (t + 1)))) (T - t - 1) (t + 1)
            (p.1, z) ∂p.2.toMeasure) := by
      have hf : LowerSemicontinuous
          (fun q : PairHist X Y t × (X (t + 1) × Y (t + 1)) =>
            VGo c (fun t x => (κμP t x : Measure (X (t + 1))))
              (fun t y => (κνP t y : Measure (Y (t + 1)))) (T - t - 1)
              (t + 1) (q.1, q.2)) :=
        lowerSemicontinuous_VGo κμP κνP c hκμ_cont hκν_cont hc
          (T - t - 1) (t + 1)
      exact lowerSemicontinuous_lintegral_prodMk hf
    exact WeakP.exists_measurable_selection
      (fun h => argminSet_nonempty κμP κνP t hF h)
      (fun h => isClosed_argminSet κμP κνP t hF h)
      (fun U hU => measurableSet_argminSet_hit κμP κνP hκμ_cont hκν_cont
        t hF hU)
  choose φ hφmeas hφmem using key
  refine ⟨fun t h => (φ t h).toMeasure,
    fun t h => (hφmem t h).1,
    fun t h => ?_,
    fun t => ⟨φ t, hφmeas t, fun h => rfl⟩⟩
  rw [iInf_feas_eq_iInf_feasGraph _ _ (fun _ _ => inferInstance) t h]
  refine le_trans ((hφmem t h).2) ?_
  exact le_iInf₂ fun γ hγ => iInf₂_le γ ⟨hγ, Set.mem_univ γ⟩
end MultiPeriod
