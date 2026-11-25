-- Prove2me | solution 1 for GroundTheory.LocalField.qcpow_mul_qcpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:18:03.92407+00:00
-- url     : https://prove2.me/submissions/bc42452e-b782-4ff8-b193-32715939974b

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
theorem _root_.solution (a b : ℂ) :
    (residueCard K : ℂ) ^ a * (residueCard K : ℂ) ^ b = (residueCard K : ℂ) ^ (a + b) :=
  (Complex.cpow_add _ _ residueCard_ne_zero_complex).symm
end GroundTheory.LocalField
