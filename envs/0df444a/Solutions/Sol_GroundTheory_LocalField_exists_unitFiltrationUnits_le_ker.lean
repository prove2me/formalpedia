-- Prove2me | solution 1 for GroundTheory.LocalField.exists_unitFiltrationUnits_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:52:33.446214+00:00
-- url     : https://prove2.me/submissions/425987cf-8c7f-41aa-943d-49bd198a3516

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaShell
import Definitions.Def_GroundTheory_LocalFields_LocalZetaChar
import Theorems.Thm_GroundTheory_Global_Complex_units_noSmallSubgroups
import Theorems.Thm_GroundTheory_Global_isOpen_ker_of_noSmallSubgroups
import Theorems.Thm_GroundTheory_LocalField_exists_unitFiltrationUnits_le
import Theorems.Thm_GroundTheory_LocalField_hasBasis_nhds_one_unitFiltrationUnits
import Theorems.Thm_GroundTheory_LocalField_isOpen_unitFiltrationUnits


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
theorem _root_.solution : ∃ n, unitFiltrationUnits K n ≤ χ.ker := by
  refine exists_unitFiltrationUnits_le (GroundTheory.Global.isOpen_ker_of_noSmallSubgroups (fun W hW => ?_)
    GroundTheory.Global.Complex.units_noSmallSubgroups χ hχ)
  obtain ⟨n, -, hn⟩ := hasBasis_nhds_one_unitFiltrationUnits.mem_iff.mp hW
  exact ⟨⟨unitFiltrationUnits K n, isOpen_unitFiltrationUnits n⟩, hn⟩
end GroundTheory.LocalField
