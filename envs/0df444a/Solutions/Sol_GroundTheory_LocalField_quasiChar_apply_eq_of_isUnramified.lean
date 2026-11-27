-- Prove2me | solution 1 for GroundTheory.LocalField.quasiChar_apply_eq_of_isUnramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:47:01.642636+00:00
-- url     : https://prove2.me/submissions/3ad0fe84-89ec-40b9-9588-aad2cb9f5c5e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaShell
import Definitions.Def_GroundTheory_LocalFields_LocalZetaChar
import Theorems.Thm_GroundTheory_LocalField_quasiChar_apply_of_isUnramified

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
theorem _root_.solution (h : IsUnramifiedChar χ) {π : Kˣ}
    (hπ : ord (π : K) = 1) : χ π = χ (unifUnit K) := by
  rw [quasiChar_apply_of_isUnramified h, hπ, zpow_one]
end GroundTheory.LocalField
