-- Prove2me | solution 1 for MultiPeriod.exists_measurable_feasible_strategy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:34:31.6748+00:00
-- url     : https://prove2.me/submissions/6530fd7f-5173-4f02-a8d4-eafa4c23216b

import Definitions.Def_BicausalOT_LscBellman
import Definitions.Def_BicausalOT_MeasurableFeasibleStrategy
import Theorems.Thm_MultiPeriod_measurableSet_feasGraph_fiber_hit_of_measurable
import Theorems.Thm_MultiPeriod_isCompact_feasGraph_fiber
import Theorems.Thm_P2M_MultiPeriod_feasGraph_fiber_nonempty__29fdcaa9c5cf
import Theorems.Thm_WeakP_exists_measurable_selection
import Theorems.Thm_exists_measurable_selection


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
      _ _ (κνP t)) :
    ∃ γfeas : Strat X Y,
      (∀ t h, γfeas t h ∈ Feas (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t h) ∧
      (∀ t, ∃ φ : PairHist X Y t → WeakP (X (t + 1) × Y (t + 1)),
        Measurable φ ∧ ∀ h, γfeas t h = (φ h).toMeasure) := by
  have key : ∀ t : ℕ, ∃ φ : PairHist X Y t → WeakP (X (t + 1) × Y (t + 1)),
      Measurable φ ∧ ∀ h, (h, φ h) ∈ FeasGraph
        (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t := by
    intro t
    exact WeakP.exists_measurable_selection
      (fun h => feasGraph_fiber_nonempty' κμP κνP t h)
      (fun h => (isCompact_feasGraph_fiber κμP κνP t h).isClosed)
      (fun U hU => measurableSet_feasGraph_fiber_hit_of_measurable
        κμP κνP hκμ_measW hκν_measW t hU)
  choose φ hφmeas hφmem using key
  exact ⟨fun t h => (φ t h).toMeasure,
    fun t h => hφmem t h,
    fun t => ⟨φ t, hφmeas t, fun h => rfl⟩⟩
end MultiPeriod
