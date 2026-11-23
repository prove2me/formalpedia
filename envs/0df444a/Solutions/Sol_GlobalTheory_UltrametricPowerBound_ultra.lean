-- Prove2me | solution 1 for GlobalTheory.UltrametricPowerBound.ultra
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:38.019707+00:00
-- url     : https://prove2.me/submissions/7fc65f0a-8592-4727-8c05-373ad9740891

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowSubOneLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UltrametricPowerBound
variable {l : ℕ} [Fact (Nat.Prime l)]
namespace GlobalTheory.UltrametricPowerBound
theorem _root_.solution (q r : ℚ_[l]) : ‖q + r‖ ≤ max ‖q‖ ‖r‖ := Padic.nonarchimedean q r
end GlobalTheory.UltrametricPowerBound
