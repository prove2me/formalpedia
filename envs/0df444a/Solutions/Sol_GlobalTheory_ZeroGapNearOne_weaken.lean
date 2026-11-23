-- Prove2me | solution 1 for GlobalTheory.ZeroGapNearOne.weaken
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:45.899497+00:00
-- url     : https://prove2.me/submissions/223769e1-379c-47f3-a590-3ee2f3181891

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLeNormLFunctionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsNormDerivLFunctionLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionConjEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZeroFreePrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsDirichletLFunctionZeroGapNearOne
import Theorems.Thm_GlobalTheory_ZeroGapNearOne_log_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.ZeroGapNearOne
namespace GlobalTheory.ZeroGapNearOne
theorem _root_.solution {x c d : ℝ} (hx : 1 ≤ x) (hc : 0 < c) (hcd : c ≤ d) :
    c / (x ^ 2 * Real.log (3 * x)) ≤ d / Real.log (3 * x) := by
  have hL := log_pos hx
  have h2 : 1 ≤ x ^ 2 := one_le_pow₀ hx
  apply div_le_div₀ (by linarith) hcd hL
  nlinarith
end GlobalTheory.ZeroGapNearOne
