-- Prove2me | solution 1 for GroundTheory.LocalField.qcpow_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:18:41.05609+00:00
-- url     : https://prove2.me/submissions/29f7c719-0f8f-4d9a-8a40-3c6d59e8a02a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Theorems.Thm_GroundTheory_LocalField_residueCard_ne_zero_complex


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
theorem _root_.solution (z : ℂ) (n : ℤ) :
    ((residueCard K : ℂ) ^ z) ^ n = (residueCard K : ℂ) ^ ((n : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero residueCard_ne_zero_complex,
    Complex.cpow_def_of_ne_zero residueCard_ne_zero_complex, ← Complex.exp_int_mul]
  ring_nf
end GroundTheory.LocalField
