-- Prove2me | solution 1 for GlobalTheory.ExceptionalPair.log_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:48.300063+00:00
-- url     : https://prove2.me/submissions/ccc36edf-919b-47ed-869f-7b72b83e3fc1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionConjEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_OrderNeTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZeroFreePrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsDirichletLFunctionZeroGapNearOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DirichletLZerosEqPrimitiveCharacterZerosStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExceptionalDirichletZeroUniqueZeroFreeRegion

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
open GlobalTheory GlobalTheory.ExceptionalPair
namespace GlobalTheory.ExceptionalPair
theorem _root_.solution {M : ℕ} (hM : 3 ≤ M) {a : ℝ} (ha : 0 < a) (ha3 : a ≤ 3) :
    Real.log (a * M) ≤ 2 * Real.log M := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  rw [Real.log_mul ha.ne' hM0.ne']
  have := Real.log_le_log ha (show a ≤ (M : ℝ) by linarith)
  linarith
end GlobalTheory.ExceptionalPair
