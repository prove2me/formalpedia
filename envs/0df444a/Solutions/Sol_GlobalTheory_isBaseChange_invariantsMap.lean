-- Prove2me | solution 1 for GlobalTheory.isBaseChange_invariantsMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:48.296125+00:00
-- url     : https://prove2.me/submissions/6ee5d5a8-8033-41ce-a063-b420383073d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_isBaseChange_of_forall_eq

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
    (ρ' : Representation S G M') (f : M →ₗ[R] M') (hb : IsBaseChange S f)
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) : IsBaseChange S (invariantsMap ρ ρ' f hf) :=
  isBaseChange_of_forall_eq S (ι := G) (fun g ↦ ρ g) (fun _ ↦ .id) (fun g ↦ ρ' g) (fun _ ↦ .id)
    f hb (fun _ ↦ f) (fun _ ↦ hb) hf (fun _ _ ↦ rfl) ρ.invariants.subtype
    Subtype.val_injective (fun x ↦ by simp [Representation.mem_invariants])
    ρ'.invariants.subtype Subtype.val_injective
    (fun x ↦ by simp [Representation.mem_invariants]) _ (fun _ ↦ rfl)
end GlobalTheory
