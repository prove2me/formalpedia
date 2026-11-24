-- Prove2me | solution 1 for GlobalTheory.T.exists_field_coeff_norm_sum_smul_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:50:02.635446+00:00
-- url     : https://prove2.me/submissions/06051f10-74c0-483f-8bd4-1c2aaa57f443

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsFieldCombinationNormNeZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsFieldCombinationNormNeZeroStatement
import Theorems.Thm_GlobalTheory_exists_field_combination_norm_ne_zero


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
theorem _root_.solution : ∀ {k B A : Type} [inst : Field k] [Infinite k] [inst_2 : CommRing B] [IsDomain B] [inst_4 : Algebra k B] [inst_5 : CommRing A] [inst_6 : Algebra B A] [Module.Free B A] [Module.Finite B A] {d : ℕ} (y : Fin d → A), (∃ x : Fin d → B, Algebra.norm B (∑ i, x i • y i) ≠ 0) → ∃ a : Fin d → k, Algebra.norm B (∑ i, algebraMap k B (a i) • y i) ≠ 0 := by
  first | exact @GlobalTheory.exists_field_combination_norm_ne_zero | exact GlobalTheory.exists_field_combination_norm_ne_zero | (intros; apply GlobalTheory.exists_field_combination_norm_ne_zero <;> assumption)
end _root_.GlobalTheory.T
