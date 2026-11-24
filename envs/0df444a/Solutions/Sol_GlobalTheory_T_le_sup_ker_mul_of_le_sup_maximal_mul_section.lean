-- Prove2me | solution 1 for GlobalTheory.T.le_sup_ker_mul_of_le_sup_maximal_mul_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:29:51.836116+00:00
-- url     : https://prove2.me/submissions/8b96ec27-91e3-4ca3-9433-d9f639d0c84d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeSupKerMulOfLeSupMaximalMulSection
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeSupKerMulOfLeSupMaximalMulSectionStatement
import Theorems.Thm_GlobalTheory_nakayama_at_section


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
theorem _root_.solution : ∀ (O P : Type) [CommRing O] [IsLocalRing O] [CommRing P] [Algebra O P] (η : P →ₐ[O] O) (J S : Ideal P), J.FG → J ≤ S ⊔ (IsLocalRing.maximalIdeal O).comap η * J → J ≤ S ⊔ RingHom.ker η * J := by
  first | exact @GlobalTheory.nakayama_at_section | exact GlobalTheory.nakayama_at_section | (intros; apply GlobalTheory.nakayama_at_section <;> assumption)
end _root_.GlobalTheory.T
