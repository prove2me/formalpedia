-- Prove2me | solution 1 for GlobalTheory.T.prod_classGroup_mk0_eq_of_linearEquiv_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:24:51.447172+00:00
-- url     : https://prove2.me/submissions/14610ca7-46bc-4558-86b0-556f0486d188

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdClassGroupMk0EqOfLinearEquivPi
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdClassGroupMk0EqOfLinearEquivPiStatement
import Theorems.Thm_GlobalTheory_prod_classGroup_mk0_eq_of_pi_linearEquiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (ι : Type) [Fintype ι] (I J : ι → (Ideal R)⁰), Nonempty (((i : ι) → (I i : Ideal R)) ≃ₗ[R] ((i : ι) → (J i : Ideal R))) → ∏ i, ClassGroup.mk0 (I i) = ∏ i, ClassGroup.mk0 (J i) := by
  first | exact @GlobalTheory.prod_classGroup_mk0_eq_of_pi_linearEquiv | exact GlobalTheory.prod_classGroup_mk0_eq_of_pi_linearEquiv | (intros; apply GlobalTheory.prod_classGroup_mk0_eq_of_pi_linearEquiv <;> assumption)
end _root_.GlobalTheory.T
