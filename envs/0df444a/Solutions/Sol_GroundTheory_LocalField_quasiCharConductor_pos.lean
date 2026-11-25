-- Prove2me | solution 1 for GroundTheory.LocalField.quasiCharConductor_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:15:19.275708+00:00
-- url     : https://prove2.me/submissions/6d9ed3c4-2e55-4c41-aee1-b50ddb566e1e

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
omit hχ
namespace GroundTheory.LocalField
theorem _root_.solution (hχ : Continuous χ) (h : ¬ IsUnramifiedChar χ) :
    0 < quasiCharConductor χ :=
  Nat.pos_of_ne_zero (mt (quasiCharConductor_eq_zero_iff hχ).mp h)
end GroundTheory.LocalField
