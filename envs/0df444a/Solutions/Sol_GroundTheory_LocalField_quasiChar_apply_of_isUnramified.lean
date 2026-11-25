-- Prove2me | solution 1 for GroundTheory.LocalField.quasiChar_apply_of_isUnramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:00:23.266477+00:00
-- url     : https://prove2.me/submissions/e35ad8b2-5b16-4a2e-a0ee-cc656baf11b8

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaShell
import Definitions.Def_GroundTheory_LocalFields_LocalZetaChar
import Theorems.Thm_GroundTheory_LocalField_unifUnit_zpow_neg_mul_mem
import Theorems.Thm_GroundTheory_LocalField_eq_unifUnit_zpow_mul

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
namespace GroundTheory.LocalField
theorem _root_.solution (h : IsUnramifiedChar χ) (u : Kˣ) :
    χ u = χ (unifUnit K) ^ ord (u : K) := by
  conv_lhs => rw [eq_unifUnit_zpow_mul u]
  rw [map_mul, MonoidHom.mem_ker.mp (h (unifUnit_zpow_neg_mul_mem u)), mul_one, map_zpow]
end GroundTheory.LocalField
