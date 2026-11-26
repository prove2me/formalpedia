-- Prove2me | solution 1 for NagataFactoriality.nagata_theorem_of_prime_or_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:02:51.150784+00:00
-- url     : https://prove2.me/submissions/103c1a36-ac3c-431c-a25a-9e4ba8420184

import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Definitions.Def_NagataFactoriality_Nagata_Theorem
import Theorems.Thm_NagataFactoriality_Submonoid_zero_notMem_of_prime_or_unit
import Theorems.Thm_NagataFactoriality_hasFactorization_of_noetherian
import Theorems.Thm_NagataFactoriality_nagata_key_lemma_isLocalization


set_option autoImplicit false
open NagataFactoriality
namespace NagataFactoriality
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (S : Submonoid R) (hS : ∀ s ∈ S, Prime s ∨ IsUnit s)
    (hUFD :
      @UniqueFactorizationMonoid (Localization S)
        (by
          letI : Fact ((0 : R) ∉ S) := ⟨Submonoid.zero_notMem_of_prime_or_unit hS⟩
          infer_instance)) :
    UniqueFactorizationMonoid R := by
  letI : Fact ((0 : R) ∉ S) := ⟨Submonoid.zero_notMem_of_prime_or_unit hS⟩
  letI : UniqueFactorizationMonoid (Localization S) := hUFD
  exact ufd_of_factorization_and_primes
    (hasFactorization_of_noetherian (α := R))
    (fun p hp => nagata_key_lemma_isLocalization
      (S := S) (β := Localization S) hS hp)
end NagataFactoriality
