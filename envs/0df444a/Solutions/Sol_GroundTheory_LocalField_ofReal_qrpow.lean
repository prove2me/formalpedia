-- Prove2me | solution 1 for GroundTheory.LocalField.ofReal_qrpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:25:13.767371+00:00
-- url     : https://prove2.me/submissions/e1081082-2f51-4e0b-9395-c36530c2f921

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Theorems.Thm_GroundTheory_LocalField_residueCard_pos_real


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
theorem _root_.solution (r : ℝ) :
    (((residueCard K : ℝ) ^ r : ℝ) : ℂ) = (residueCard K : ℂ) ^ (r : ℂ) := by
  rw [Complex.ofReal_cpow residueCard_pos_real.le, Complex.ofReal_natCast]
end GroundTheory.LocalField
