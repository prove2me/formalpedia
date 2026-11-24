-- Prove2me | solution 1 for GlobalTheory.mem_baseChange_invariants_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:39:45.839215+00:00
-- url     : https://prove2.me/submissions/acc0f300-f599-4df8-b09b-3c1d962fe19a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_span_image_invariants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [Module S M']
  [IsScalarTower R S M']
variable {G : Type*} [Group G]
namespace GlobalTheory
theorem _root_.solution [Finite G] [Module.Flat R S] (ρ : Representation R G M)
    (x : S ⊗[R] M) :
    x ∈ ρ.invariants.baseChange S ↔ ∀ g, (ρ g).baseChange S x = x := by
  let ρ' : Representation S G (S ⊗[R] M) := (Module.End.baseChangeHom R S M).toMonoidHom.comp ρ
  have := span_image_invariants S ρ ρ' (TensorProduct.mk R S M 1)
    (TensorProduct.isBaseChange R M S) (fun g x ↦ rfl)
  rw [Submodule.baseChange_eq_span]
  exact (SetLike.ext_iff.mp this x)
end GlobalTheory
