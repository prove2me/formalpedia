-- Prove2me | solution 1 for GlobalTheory.HermFrame.Model.blockQQ_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:46:27.215904+00:00
-- url     : https://prove2.me/submissions/bde442b5-c48b-44d6-bce2-d666d83a3f7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CurvSubQuotTautPairGram
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.HermFrame.Model
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
  {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}
namespace GlobalTheory.HermFrame.Model
theorem _root_.solution (K T : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    blockQQ K T = T.toBlocks₂₂ - T.toBlocks₂₁ * orthCoeff K := by
  conv_lhs => rw [← fromBlocks_toBlocks T]
  simp [blockQQ, quotMap, orthLift, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  abel
end GlobalTheory.HermFrame.Model
