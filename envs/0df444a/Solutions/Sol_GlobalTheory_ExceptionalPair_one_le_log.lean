-- Prove2me | solution 1 for GlobalTheory.ExceptionalPair.one_le_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:07.06296+00:00
-- url     : https://prove2.me/submissions/83789463-7ec0-4a34-9dc4-cad9795cd1bf

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
theorem _root_.solution {M : ℕ} (hM : 3 ≤ M) : 1 ≤ Real.log M := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_d9]
end GlobalTheory.ExceptionalPair
