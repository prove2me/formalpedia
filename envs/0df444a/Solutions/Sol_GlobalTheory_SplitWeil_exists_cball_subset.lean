-- Prove2me | solution 1 for GlobalTheory.SplitWeil.exists_cball_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:48.563952+00:00
-- url     : https://prove2.me/submissions/54c8c9c6-1e79-42b7-be77-5952c4cf6e7b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
namespace GlobalTheory.SplitWeil
theorem _root_.solution {U : Set k} (hU : U ∈ 𝓝 (0 : k)) : ∃ s : kˣ, cball s ⊆ U := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff U).mp hU
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero k)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact γ.ne_zero (by simpa using hy.symm)
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hr0 : r ≠ 0 := by simpa using hr
  refine ⟨Units.mk0 (r * y) (mul_ne_zero hr0 hy0), fun z hz => hγ ?_⟩
  have hz' : valuation k z ≤ valuation k (r * y) := hz
  refine lt_of_le_of_lt hz' ?_
  rw [map_mul, hy]
  exact mul_lt_of_lt_one_left (by simp [zero_lt_iff]) hr1
end GlobalTheory.SplitWeil
