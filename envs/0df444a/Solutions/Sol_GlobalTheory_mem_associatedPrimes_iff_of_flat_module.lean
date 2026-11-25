-- Prove2me | solution 1 for GlobalTheory.mem_associatedPrimes_iff_of_flat_module
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:52:34.786828+00:00
-- url     : https://prove2.me/submissions/851fe59f-4168-4f78-9eef-c9d0e2b6ba2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
import Theorems.Thm_GlobalTheory_under_mem_associatedPrimes
import Theorems.Thm_GlobalTheory_associatedPrimes_subset_of_flat
import Theorems.Thm_GlobalTheory_mem_associatedPrimes_tensor_quotient_under
import Theorems.Thm_GlobalTheory_associatedPrimes_tensor_residueField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {M : Type*} [AddCommGroup M] [Module A M]
variable [Module B M] [IsScalarTower A B M] [Module.Flat A M]
namespace GlobalTheory
theorem _root_.solution [IsNoetherianRing A] (q : Ideal B) [q.IsPrime] :
    q ∈ associatedPrimes B M ↔ q.under A ∈ associatedPrimes A A ∧
      q ∈ associatedPrimes B (M ⊗[A] (q.under A).ResidueField) := by
  rw [associatedPrimes_tensor_residueField]
  have e := LinearEquiv.AssociatedPrimes.eq (AlgebraTensorModule.rid A B M)
  constructor
  · intro hq
    refine ⟨associatedPrimes_subset_of_flat (under_mem_associatedPrimes hq), ?_⟩
    rw [← e] at hq
    exact mem_associatedPrimes_tensor_quotient_under hq
  · rintro ⟨hp, hq⟩
    obtain ⟨-, f, hf⟩ := (isAssociatedPrime_iff_exists_injective_linearMap _ _).1 hp
    have hf' : Function.Injective (AlgebraTensorModule.lTensor B M f) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ hf
    rw [← e]
    exact associatedPrimes.subset_of_injective hf' hq
end GlobalTheory
