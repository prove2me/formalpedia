-- Prove2me | solution 1 for GroundTheory.LocalField.unitFiltrationUnits_quasiCharConductor_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:59:48.699284+00:00
-- url     : https://prove2.me/submissions/b5efd42a-ca7a-4b50-bd6f-43f4d13f93d2

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaShell
import Definitions.Def_GroundTheory_LocalFields_LocalZetaChar
import Theorems.Thm_GroundTheory_LocalField_exists_unitFiltrationUnits_le_ker

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
theorem _root_.solution :
    unitFiltrationUnits K (quasiCharConductor χ) ≤ χ.ker :=
  Nat.sInf_mem (exists_unitFiltrationUnits_le_ker hχ)
end GroundTheory.LocalField
