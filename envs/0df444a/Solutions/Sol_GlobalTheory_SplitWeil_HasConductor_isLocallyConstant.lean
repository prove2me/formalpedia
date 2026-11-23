-- Prove2me | solution 1 for GlobalTheory.SplitWeil.HasConductor.isLocallyConstant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:32.767317+00:00
-- url     : https://prove2.me/submissions/74e66d84-9091-4977-909b-04cdbc4e98ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_eq_one

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
variable {ψ : AddChar k Circle} {c : kˣ}
namespace GlobalTheory.SplitWeil
namespace HasConductor
theorem _root_.solution (h : HasConductor ψ c) : IsLocallyConstant ψ := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  have : (fun z => -x + z) ⁻¹' cball c ∈ 𝓝 x :=
    ((isOpen_cball c).preimage (by fun_prop)).mem_nhds (by simp [cball])
  filter_upwards [this] with z hz
  have h1 := h.eq_one hz
  have h2 : z = x + (-x + z) := by ring
  rw [h2, AddChar.map_add_eq_mul, h1, mul_one]
end HasConductor
end GlobalTheory.SplitWeil
