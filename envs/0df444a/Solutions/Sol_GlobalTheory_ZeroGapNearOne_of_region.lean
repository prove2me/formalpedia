-- Prove2me | solution 1 for GlobalTheory.ZeroGapNearOne.of_region
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:28:50.048832+00:00
-- url     : https://prove2.me/submissions/45dfda94-65c3-417f-81f5-5744f4ff1a10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLeNormLFunctionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsNormDerivLFunctionLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionConjEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZeroFreePrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsDirichletLFunctionZeroGapNearOne
import Theorems.Thm_GlobalTheory_ZeroGapNearOne_log_pos
import Theorems.Thm_GlobalTheory_ZeroGapNearOne_weaken

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
theorem _root_.solution {x c d t r : ℝ} (hx : 1 ≤ x) (hc : 0 < c) (hcd : c ≤ d) (ht : |t| ≤ 1)
    (h : r < 1 - d / Real.log (x * (|t| + 2))) :
    c / (x ^ 2 * Real.log (3 * x)) ≤ 1 - r := by
  have h0 := abs_nonneg t
  have h1 : 0 < Real.log (x * (|t| + 2)) := Real.log_pos (by nlinarith)
  have h2 : Real.log (x * (|t| + 2)) ≤ Real.log (3 * x) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have h3 : d / Real.log (3 * x) ≤ d / Real.log (x * (|t| + 2)) :=
    div_le_div_of_nonneg_left (by linarith) h1 h2
  have := weaken hx hc hcd
  linarith
end GlobalTheory.ZeroGapNearOne
