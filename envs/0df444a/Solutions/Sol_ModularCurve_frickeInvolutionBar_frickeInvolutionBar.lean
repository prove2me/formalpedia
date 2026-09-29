-- Prove2me | solution 1 for ModularCurve.frickeInvolutionBar_frickeInvolutionBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/dcf5a521-0d06-53a6-92ae-8e9d7404a982

import Definitions.Def_ModularCurve_CuspidalClass
import Theorems.Thm_ModularCurve_frickeInvolutionFull_symm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_frickeInvolutionBar_frickeInvolutionBar
open ModularCurve

theorem solution (N : ℕ) [NeZero N] (y : ModularCurve.modularFunctionFieldBar N) : ModularCurve.frickeInvolutionBar N (ModularCurve.frickeInvolutionBar N y) = y := by
  have hfix : ∀ z, frickeInvolutionFull N (frickeInvolutionFull N z) = z := fun z => by
    nth_rewrite 1 [← frickeInvolutionFull_symm N]
    exact AlgEquiv.symm_apply_apply _ _
  have hsq : frickeInvolutionFull N * frickeInvolutionFull N = 1 := AlgEquiv.ext fun z => by
    rw [AlgEquiv.mul_apply, hfix, AlgEquiv.one_apply]
  rw [frickeInvolutionBar_def, ← AlgEquiv.mul_apply, ← map_mul, hsq, map_one, AlgEquiv.one_apply]

end S_ModularCurve_frickeInvolutionBar_frickeInvolutionBar
end P2MW
export P2MW.S_ModularCurve_frickeInvolutionBar_frickeInvolutionBar (solution)
