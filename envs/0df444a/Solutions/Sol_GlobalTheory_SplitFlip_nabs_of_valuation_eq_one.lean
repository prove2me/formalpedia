-- Prove2me | solution 1 for GlobalTheory.SplitFlip.nabs_of_valuation_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:23:28.105653+00:00
-- url     : https://prove2.me/submissions/eae8af73-91dc-4848-b82c-880306faf60c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_le_one
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_mul
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_one
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SplitFlip
theorem _root_.solution {x : kˣ} (hx : valuation k (x : k) = 1) : nabs k x = 1 := by
  borelize k
  have h1 := nabs_le_one x hx.le
  have h2 := nabs_le_one x⁻¹ (by simp [hx])
  have h3 : nabs k x * nabs k x⁻¹ = 1 := by rw [← nabs_mul]; simp [nabs_one]
  nlinarith [nabs_pos x, nabs_pos x⁻¹]
end GlobalTheory.SplitFlip
