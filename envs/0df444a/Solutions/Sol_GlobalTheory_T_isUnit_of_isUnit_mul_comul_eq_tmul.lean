-- Prove2me | solution 1 for GlobalTheory.T.isUnit_of_isUnit_mul_comul_eq_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:22:45.147+00:00
-- url     : https://prove2.me/submissions/930f9a0b-3545-43d3-915c-17eb8555dfa7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOfUnitMulComulEqTmulSelf
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOfUnitMulComulEqTmulSelfStatement
import Theorems.Thm_GlobalTheory_isUnit_of_unit_mul_comul_eq_tmul_self


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
theorem _root_.solution : ∀ (K H : Type) [Field K] [CommRing H] [HopfAlgebra K H] (c : H ⊗[K] H), IsUnit c → ∀ u : H, u ≠ 0 → c * Coalgebra.comul (R := K) u = u ⊗ₜ[K] u → IsUnit u := by
  first | exact @GlobalTheory.isUnit_of_unit_mul_comul_eq_tmul_self | exact GlobalTheory.isUnit_of_unit_mul_comul_eq_tmul_self | (intros; apply GlobalTheory.isUnit_of_unit_mul_comul_eq_tmul_self <;> assumption)
end _root_.GlobalTheory.T
