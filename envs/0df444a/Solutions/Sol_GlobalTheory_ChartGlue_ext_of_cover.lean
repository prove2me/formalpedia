-- Prove2me | solution 1 for GlobalTheory.ChartGlue.ext_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:30:42.858435+00:00
-- url     : https://prove2.me/submissions/58645f66-f6c1-4e9f-a3c2-958f5c0cd59c

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ChartMeasApplyOfSubset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ContDiff ENNReal
open GlobalTheory GlobalTheory.ChartGlue
variable {n : ℕ} {X : Type*} [TopologicalSpace X] {ι : Type*}
variable [MeasurableSpace X]
variable [BorelSpace X]
variable [SecondCountableTopology X]
namespace GlobalTheory.ChartGlue
theorem _root_.solution {μ ν : Measure X} (S : ι → Set X) (hS : ∀ i, IsOpen (S i))
    (hc : ∀ y, ∃ i, y ∈ S i) (h : ∀ i A, MeasurableSet A → A ⊆ S i → μ A = ν A) : μ = ν := by
  obtain ⟨T, hT, hTS⟩ := TopologicalSpace.isOpen_iUnion_countable S hS
  refine Measure.ext_of_biUnion_eq_univ hT (hTS.trans (iUnion_eq_univ_iff.2 hc)) fun i _ => ?_
  ext A hA
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  exact h i _ (hA.inter (hS i).measurableSet) inter_subset_right
end GlobalTheory.ChartGlue
