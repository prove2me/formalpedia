-- Prove2me | solution 1 for GlobalTheory.T.trdeg_tensor_complex_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:33:46.183073+00:00
-- url     : https://prove2.me/submissions/2070fc02-d0ca-49b4-b060-51f2f846acd1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TrdegComplexBaseChangeEq
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TrdegComplexBaseChangeEqStatement
import Theorems.Thm_GlobalTheory_trdeg_complex_baseChange_eq


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
theorem _root_.solution : ∀ {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ'] [IsDomain (K ⊗[ℂ] κ')], Algebra.trdeg K (K ⊗[ℂ] κ') = Algebra.trdeg ℂ κ' := by
  first | exact @GlobalTheory.trdeg_complex_baseChange_eq | exact GlobalTheory.trdeg_complex_baseChange_eq | (intros; apply GlobalTheory.trdeg_complex_baseChange_eq <;> assumption)
end _root_.GlobalTheory.T
