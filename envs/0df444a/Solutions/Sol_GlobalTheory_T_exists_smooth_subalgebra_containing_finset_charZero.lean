-- Prove2me | solution 1 for GlobalTheory.T.exists_smooth_subalgebra_containing_finset_charZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:16:15.29486+00:00
-- url     : https://prove2.me/submissions/6c5cdd3a-923f-4d29-9d9f-7e14a78f94a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmoothSubalgebraContainingFinsetCharZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmoothSubalgebraContainingFinsetCharZeroStatement
import Theorems.Thm_GlobalTheory_exists_smooth_subalgebra_of_finset


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
theorem _root_.solution : ∀ (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] (s : Finset K), ∃ R : Subalgebra F K, (↑s : Set K) ⊆ (R : Set K) ∧ Algebra.Smooth F R := by
  first | exact @GlobalTheory.exists_smooth_subalgebra_of_finset | exact GlobalTheory.exists_smooth_subalgebra_of_finset | (intros; apply GlobalTheory.exists_smooth_subalgebra_of_finset <;> assumption)
end _root_.GlobalTheory.T
