-- Prove2me | solution 1 for GlobalTheory.ZeroGapNearOne.log_le_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:20:10.520617+00:00
-- url     : https://prove2.me/submissions/26347ac7-b1df-4262-98e9-7b0646b8404b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLeNormLFunctionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsNormDerivLFunctionLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionConjEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZeroFreePrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsDirichletLFunctionZeroGapNearOne

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
theorem _root_.solution {x : ℝ} (hx : 1 ≤ x) : Real.log (3 * x) ≤ 4 * √x := by
  have hs : 0 < √x := Real.sqrt_pos.2 (by linarith)
  have hsq : √x * √x = x := Real.mul_self_sqrt (by linarith)
  have h1 : Real.log (3 * x) ≤ Real.log ((2 * √x) ^ 2) :=
    Real.log_le_log (by linarith) (by nlinarith)
  rw [Real.log_pow] at h1
  have h2 := Real.log_le_sub_one_of_pos (show 0 < 2 * √x by positivity)
  push_cast at h1
  linarith
end GlobalTheory.ZeroGapNearOne
