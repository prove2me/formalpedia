-- Prove2me | solution 1 for GroundTheory.LocalField.modulus_cpow_eq_qcpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:25:09.236305+00:00
-- url     : https://prove2.me/submissions/8a5cecc5-18c0-4891-8be1-32089f6f0ede

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Theorems.Thm_GroundTheory_LocalField_qcpow_zpow
import Theorems.Thm_GroundTheory_LocalField_modulus_cpow_eq_zpow


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
namespace GroundTheory.LocalField
theorem _root_.solution {x : K} (hx : x ≠ 0) (z : ℂ) :
    ((modulus x : ℝ) : ℂ) ^ z = (residueCard K : ℂ) ^ (-(ord x : ℂ) * z) := by
  have := modulus_cpow_eq_zpow (Units.mk0 x hx) z
  rw [Units.val_mk0] at this
  rw [this, qcpow_zpow]
  congr 1
  ring
end GroundTheory.LocalField
