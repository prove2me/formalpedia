-- Prove2me | solution 1 for GlobalTheory.T.exists_norm_sum_smul_ne_zero_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:48:55.009801+00:00
-- url     : https://prove2.me/submissions/0904ce00-22d1-471f-82f5-ef2df00edc7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsCombinationNormNeZeroOfLinearIndependentAl
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsCombinationNormNeZeroOfLinearIndependentAlStatement
import Theorems.Thm_GlobalTheory_exists_combination_norm_ne_zero_of_linearIndependent


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {B A : Type} [inst : CommRing B] [IsDomain B] [inst_2 : CommRing A] [inst_3 : Algebra B A] [Module.Free B A] [Module.Finite B A] {d : ℕ}, Module.finrank B A = d → ∀ (y : Fin d → A), LinearIndependent B y → ∃ x : Fin d → B, Algebra.norm B (∑ i, x i • y i) ≠ 0 := by
  first | exact @GlobalTheory.exists_combination_norm_ne_zero_of_linearIndependent | exact GlobalTheory.exists_combination_norm_ne_zero_of_linearIndependent | (intros; apply GlobalTheory.exists_combination_norm_ne_zero_of_linearIndependent <;> assumption)
end _root_.GlobalTheory.T
