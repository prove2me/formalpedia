-- Prove2me | solution 1 for GlobalTheory.FiniteCovolume.measure_le_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:02:42.136115+00:00
-- url     : https://prove2.me/submissions/ccd3d433-1288-485d-bf2a-16dde6d0390f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FinMuOfFiniteCovolume
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.FiniteCovolume
namespace GlobalTheory.FiniteCovolume
theorem _root_.solution {G ι : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    [Countable ι] (ν : Measure G) [ν.IsMulLeftInvariant] (ρ : ι → G) {T Ω : Set G}
    (hT : MeasurableSet T) (hΩ : MeasurableSet Ω) (hcov : ∀ g, ∃ i, ∃ w ∈ Ω, g = ρ i * w)
    (huniq : ∀ w i j, ρ i * w ∈ T → ρ j * w ∈ T → i = j) : ν T ≤ ν Ω := by
  classical
  have hS : ∀ i, MeasurableSet (Ω ∩ (fun w => ρ i * w) ⁻¹' T) := fun i =>
    hΩ.inter (measurable_const_mul (ρ i) hT)
  have hdisj : Pairwise (Function.onFun Disjoint fun i => Ω ∩ (fun w => ρ i * w) ⁻¹' T) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    rintro w ⟨_, hi⟩ ⟨_, hj⟩
    exact hij (huniq w i j hi hj)
  have hsub : T ⊆ ⋃ i, (fun w => ρ i * w) '' (Ω ∩ (fun w => ρ i * w) ⁻¹' T) := by
    intro g hg
    obtain ⟨i, w, hw, rfl⟩ := hcov g
    exact Set.mem_iUnion.2 ⟨i, w, ⟨hw, hg⟩, rfl⟩
  calc ν T ≤ ν (⋃ i, (fun w => ρ i * w) '' (Ω ∩ (fun w => ρ i * w) ⁻¹' T)) := measure_mono hsub
    _ ≤ ∑' i, ν ((fun w => ρ i * w) '' (Ω ∩ (fun w => ρ i * w) ⁻¹' T)) := measure_iUnion_le _
    _ = ∑' i, ν (Ω ∩ (fun w => ρ i * w) ⁻¹' T) := by
        congr 1
        funext i
        rw [Set.image_mul_left, measure_preimage_mul]
    _ = ν (⋃ i, Ω ∩ (fun w => ρ i * w) ⁻¹' T) := (measure_iUnion hdisj hS).symm
    _ ≤ ν Ω := measure_mono (Set.iUnion_subset fun _ => Set.inter_subset_left)
end GlobalTheory.FiniteCovolume
