-- Prove2me | solution 1 for GlobalTheory.trdeg_complex_baseChange_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:22.472466+00:00
-- url     : https://prove2.me/submissions/de6491ed-ebd4-4f07-afc0-4462618247e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TrdegComplexBaseChangeEq
import Theorems.Thm_GlobalTheory_trdeg_tensorProduct_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ'] [IsDomain (K ⊗[ℂ] κ')], Algebra.trdeg K (K ⊗[ℂ] κ') = Algebra.trdeg ℂ κ' :=
  trdeg_tensorProduct_eq
end GlobalTheory
