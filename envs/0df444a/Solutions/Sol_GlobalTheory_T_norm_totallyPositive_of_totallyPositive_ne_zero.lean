-- Prove2me | solution 1 for GlobalTheory.T.norm_totallyPositive_of_totallyPositive_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:19:38.64422+00:00
-- url     : https://prove2.me/submissions/d0214ea6-b967-4f6d-a70d-c4bfc96865d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormTotallyPositiveOfTotallyPositiveNeZero
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormTotallyPositiveOfTotallyPositiveNeZeroStatement
import Theorems.Thm_GlobalTheory_norm_pos_of_totallyPositive


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (a : E'), a ≠ 0 → (∀ φ : E' →+* ℝ, 0 < φ a) → ∀ φ : E →+* ℝ, 0 < φ (Algebra.norm E a) := by
  first | exact @GlobalTheory.norm_pos_of_totallyPositive | exact GlobalTheory.norm_pos_of_totallyPositive | (intros; apply GlobalTheory.norm_pos_of_totallyPositive <;> assumption)
end _root_.GlobalTheory.T
