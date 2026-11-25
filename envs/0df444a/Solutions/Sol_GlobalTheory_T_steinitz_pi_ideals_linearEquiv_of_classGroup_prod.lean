-- Prove2me | solution 1 for GlobalTheory.T.steinitz_pi_ideals_linearEquiv_of_classGroup_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:24:35.596189+00:00
-- url     : https://prove2.me/submissions/79bdf089-40c5-4e89-ade8-3dd0d8e4eed0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SteinitzPiIdealsLinearEquivOfClassGroupProd
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SteinitzPiIdealsLinearEquivOfClassGroupProdStatement
import Theorems.Thm_GlobalTheory_SteinitzProd_steinitz


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (ι : Type) [Fintype ι] (I J : ι → (Ideal R)⁰), ∏ i, ClassGroup.mk0 (I i) = ∏ i, ClassGroup.mk0 (J i) → Nonempty (((i : ι) → (I i : Ideal R)) ≃ₗ[R] ((i : ι) → (J i : Ideal R))) := by
  first | exact @GlobalTheory.SteinitzProd.steinitz | exact GlobalTheory.SteinitzProd.steinitz | (intros; apply GlobalTheory.SteinitzProd.steinitz <;> assumption)
end _root_.GlobalTheory.T
