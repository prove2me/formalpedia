-- Prove2me | solution 1 for GlobalTheory.ExceptionalPair.le_log_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:27.576879+00:00
-- url     : https://prove2.me/submissions/623c438c-cb2f-4262-b6cd-9e4b4b32fdc4

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
theorem _root_.solution {M : ℕ} (hM : 3 ≤ M) {a : ℝ} (ha : 1 ≤ a) :
    Real.log M ≤ Real.log (a * M) := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  exact Real.log_le_log hM0 (le_mul_of_one_le_left hM0.le ha)
end GlobalTheory.ExceptionalPair
