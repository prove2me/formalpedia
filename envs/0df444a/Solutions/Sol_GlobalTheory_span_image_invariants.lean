-- Prove2me | solution 1 for GlobalTheory.span_image_invariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:33:45.153528+00:00
-- url     : https://prove2.me/submissions/0c6cad6f-718e-4f54-9238-676f2036cad3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_isBaseChange_invariantsMap

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
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) :
    Submodule.span S (f '' ρ.invariants) = ρ'.invariants := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact (invariantsMap ρ ρ' f hf ⟨x, hx⟩).2
  · intro y hy
    have key : ∀ z : ρ'.invariants, (z : M') ∈ Submodule.span S (f '' ρ.invariants) := by
      intro z
      induction z using (isBaseChange_invariantsMap S ρ ρ' f hb hf).inductionOn with
      | zero => exact zero_mem _
      | tmul m => exact Submodule.subset_span ⟨m, m.2, rfl⟩
      | smul s n hn => exact Submodule.smul_mem _ s hn
      | add a b ha hb => exact add_mem ha hb
    exact key ⟨y, hy⟩
end GlobalTheory
