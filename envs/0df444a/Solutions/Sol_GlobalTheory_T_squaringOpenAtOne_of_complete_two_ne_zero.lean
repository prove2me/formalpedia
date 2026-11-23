-- Prove2me | solution 1 for GlobalTheory.T.squaringOpenAtOne_of_complete_two_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:41.558961+00:00
-- url     : https://prove2.me/submissions/e0bfe657-062a-4ef6-a9a9-d6dc0705ba20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SquaringOpenAtOneOfCompleteTwoNeZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SquaringOpenAtOneOfCompleteTwoNeZeroStatement
import Theorems.Thm_GlobalTheory_sqOpen_of_two_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [NormedField K] [CompleteSpace K], (2 : K) ≠ 0 → SqOpen K := by
  first | exact @GlobalTheory.sqOpen_of_two_ne_zero | exact GlobalTheory.sqOpen_of_two_ne_zero | (intros; apply GlobalTheory.sqOpen_of_two_ne_zero <;> assumption)
end _root_.GlobalTheory.T
