-- Prove2me | solution 1 for GlobalTheory.exists_pic_linearEquiv_groupAlgebra_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:45:48.737504+00:00
-- url     : https://prove2.me/submissions/91826cff-fab7-4ccf-899a-3b266be7828b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UniqueFactorizationMonoidAddMonoidAlgebraOfFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct AlgebraMonoidAlgebra
open AddMonoidAlgebra CommRing
open GlobalTheory
variable (A X : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
variable [AddCommGroup X] [Module.Free ℤ X]
variable {X} (N : Type*) [AddCommGroup N] [Module (AddMonoidAlgebra A X) N]
  [Module.Invertible (AddMonoidAlgebra A X) N]
namespace GlobalTheory
theorem _root_.solution :
    ∃ M : Pic A, Nonempty (N ≃ₗ[AddMonoidAlgebra A X] AddMonoidAlgebra A X ⊗[A] M) := by
  obtain ⟨M, hM⟩ := (pic_mapAlgebra_groupAlgebra_bijective A X).2 (Pic.mk _ N)
  exact ⟨M, Pic.mk_eq_mk_iff.mp hM.symm⟩
end GlobalTheory
