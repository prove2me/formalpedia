-- Prove2me | solution 1 for GlobalTheory.T.exists_tensor_idempotent_of_algHom_to_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:55:20.141078+00:00
-- url     : https://prove2.me/submissions/5c3e3288-d8c4-454b-9179-7c81e8845885

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTensorIdempotentOfAlgHomToBase
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTensorIdempotentOfAlgHomToBaseStatement
import Theorems.Thm_GlobalTheory_exists_tensor_idem_of_algHom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E K E' : Type) [Field E] [CharZero E] [Field K] [Field E'] [Algebra E K] [Algebra E E'] [FiniteDimensional E E'] (ψ : K ⊗[E] E' →ₐ[K] K), ∃ e : K ⊗[E] E', ψ e = 1 ∧ ∀ a, e * a = algebraMap K (K ⊗[E] E') (ψ a) * e := by
  first | exact @GlobalTheory.exists_tensor_idem_of_algHom | exact GlobalTheory.exists_tensor_idem_of_algHom | (intros; apply GlobalTheory.exists_tensor_idem_of_algHom <;> assumption)
end _root_.GlobalTheory.T
