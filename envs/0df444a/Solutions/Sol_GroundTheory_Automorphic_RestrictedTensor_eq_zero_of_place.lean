-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.eq_zero_of_place
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:01:43.752876+00:00
-- url     : https://prove2.me/submissions/41269db9-7b97-4be6-b2e8-359bde5cc093

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Places
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Existence
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_commute_of_mem_adjoin
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_eq_zero_of_forall_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Filter Function Module Set PiTensorProduct
open scoped TensorProduct RestrictedProduct
variable {M : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
variable {ι : Type*} {T : ι → Set (End ℂ M)}
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (hsimple : IsSimpleUnder (⋃ v, T v))
    (hcomm : ∀ v w, v ≠ w → ∀ a ∈ T v, ∀ b ∈ T w, Commute a b) (v : ι) {N : Submodule ℂ M}
    (hN : N ≠ ⊥) (hNs : IsStable (T v) N) {a : End ℂ M} (ha : a ∈ Algebra.adjoin ℂ (T v))
    (h0 : ∀ x ∈ N, a x = 0) : a = 0 := by
  have hunion : T v ∪ (⋃ w ∈ ({v}ᶜ : Set ι), T w) = ⋃ w, T w := by
    ext t
    simp only [mem_union, mem_iUnion, mem_compl_iff, mem_singleton_iff, exists_prop]
    constructor
    · rintro (ht | ⟨w, -, ht⟩)
      exacts [⟨v, ht⟩, ⟨w, ht⟩]
    · rintro ⟨w, ht⟩
      by_cases hw : w = v
      · subst hw; exact Or.inl ht
      · exact Or.inr ⟨w, hw, ht⟩
  have hc : ∀ s ∈ T v, ∀ t ∈ ⋃ w ∈ ({v}ᶜ : Set ι), T w, Commute s t := by
    intro s hs t ht
    simp only [mem_iUnion, mem_compl_iff, mem_singleton_iff, exists_prop] at ht
    obtain ⟨w, hw, ht⟩ := ht
    exact hcomm v w (Ne.symm hw) s hs t ht
  refine eq_zero_of_forall_mem (hunion ▸ hsimple) hc hN hNs (fun t ht => ?_) h0
  exact (commute_of_mem_adjoin (fun s hs => (hc s hs t ht).symm) a ha).symm
end GroundTheory.Automorphic.RestrictedTensor
