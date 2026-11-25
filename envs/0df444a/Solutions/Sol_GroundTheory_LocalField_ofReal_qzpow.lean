-- Prove2me | solution 1 for GroundTheory.LocalField.ofReal_qzpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:38:42.466245+00:00
-- url     : https://prove2.me/submissions/b9c2e359-e2ec-4efb-a69e-a715dcb098a5

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Theorems.Thm_GroundTheory_LocalField_ofReal_qrpow

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
theorem _root_.solution (n : ℤ) :
    (((residueCard K : ℝ) ^ n : ℝ) : ℂ) = (residueCard K : ℂ) ^ (n : ℂ) := by
  rw [← Real.rpow_intCast, ofReal_qrpow]
  push_cast
  rfl
end GroundTheory.LocalField
