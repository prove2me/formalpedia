-- Prove2me | solution 1 for GroundTheory.LocalField.exists_apply_ne_one_of_not_isUnramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:20:39.251139+00:00
-- url     : https://prove2.me/submissions/a9265741-b498-4722-9216-0fa54c9b9573

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaShell
import Definitions.Def_GroundTheory_LocalFields_LocalZetaChar
import Theorems.Thm_GroundTheory_LocalField_quasiCharConductor_eq_zero_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (χ : Kˣ →* ℂˣ)
variable {χ}
variable (hχ : Continuous χ)
include hχ
namespace GroundTheory.LocalField
theorem _root_.solution (h : ¬ IsUnramifiedChar χ) :
    ∃ v ∈ unitFiltrationUnits K (quasiCharConductor χ - 1), χ v ≠ 1 := by
  have hc : quasiCharConductor χ ≠ 0 := mt (quasiCharConductor_eq_zero_iff hχ).mp h
  have hlt : quasiCharConductor χ - 1 < quasiCharConductor χ := by omega
  have hnot := Nat.notMem_of_lt_sInf hlt
  by_contra hcon
  push_neg at hcon
  exact hnot fun v hv => MonoidHom.mem_ker.mpr (hcon v hv)
end GroundTheory.LocalField
