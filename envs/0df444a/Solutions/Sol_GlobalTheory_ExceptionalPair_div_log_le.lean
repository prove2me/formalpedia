-- Prove2me | solution 1 for GlobalTheory.ExceptionalPair.div_log_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:44:51.681036+00:00
-- url     : https://prove2.me/submissions/70772365-371f-4783-8e94-4e91597ff558

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionConjEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_OrderNeTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZeroFreePrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsDirichletLFunctionZeroGapNearOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DirichletLZerosEqPrimitiveCharacterZerosStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExceptionalDirichletZeroUniqueZeroFreeRegion
import Theorems.Thm_GlobalTheory_ExceptionalPair_one_le_log
import Theorems.Thm_GlobalTheory_ExceptionalPair_log_mul_le
import Theorems.Thm_GlobalTheory_ExceptionalPair_le_log_mul

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
theorem _root_.solution {M : ℕ} (hM : 3 ≤ M) {c₁ c : ℝ} (h0 : 0 ≤ c) (h : c₁ ≤ c / 2) :
    c₁ / Real.log M ≤ c / Real.log (2 * M) := by
  have hl := log_mul_le hM (a := 2) (by norm_num) (by norm_num)
  have hpos : 0 < Real.log M := lt_of_lt_of_le one_pos (one_le_log hM)
  have hpos2 : 0 < Real.log (2 * M) := by
    linarith [le_log_mul hM (a := 2) (by norm_num)]
  rw [div_le_div_iff₀ hpos hpos2]
  nlinarith [mul_nonneg (sub_nonneg.2 h) hpos2.le, mul_nonneg h0 (sub_nonneg.2 hl)]
end GlobalTheory.ExceptionalPair
