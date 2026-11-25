-- Prove2me | solution 1 for GlobalTheory.T.exists_separable_point_of_geometrically_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:17:18.27304+00:00
-- url     : https://prove2.me/submissions/5f1b3872-afd1-4706-8de3-9d64a9de4f86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSeparablePointOfGeometricallyDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSeparablePointOfGeometricallyDomainStatement
import Theorems.Thm_GlobalTheory_SepPoint_exists_sepPoint


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
theorem _root_.solution : ∀ (k B : Type) [Field k] [CommRing B] [Algebra k B], Algebra.FiniteType k B → (∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] B)) → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧ Nonempty (B →ₐ[k] k') := by
  first | exact @GlobalTheory.SepPoint.exists_sepPoint | exact GlobalTheory.SepPoint.exists_sepPoint | (intros; apply GlobalTheory.SepPoint.exists_sepPoint <;> assumption)
end _root_.GlobalTheory.T
