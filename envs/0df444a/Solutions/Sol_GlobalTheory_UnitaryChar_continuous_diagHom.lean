-- Prove2me | solution 1 for GlobalTheory.UnitaryChar.continuous_diagHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:05:12.959172+00:00
-- url     : https://prove2.me/submissions/24999dcd-fd53-4ce0-aca4-c96b0b2de069

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CircleHomEqZpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupContinuousCharEqDetZpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.UnitaryChar
variable {n : ℕ}
namespace GlobalTheory.UnitaryChar
theorem _root_.solution : Continuous (diagHom n) := by
  refine Continuous.subtype_mk ?_ _
  exact Continuous.matrix_diagonal (continuous_pi fun i =>
    continuous_subtype_val.comp (continuous_apply i))
end GlobalTheory.UnitaryChar
